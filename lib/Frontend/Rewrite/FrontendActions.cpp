//===--- FrontendActions.cpp ----------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "clang/Rewrite/Frontend/FrontendActions.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Basic/FileManager.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/FrontendDiagnostic.h"
#include "clang/Frontend/Utils.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Parse/Parser.h"
#include "clang/Rewrite/Frontend/ASTConsumers.h"
#include "clang/Rewrite/Frontend/FixItRewriter.h"
#include "clang/Rewrite/Frontend/Rewriters.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <sstream>

using namespace clang;

//===----------------------------------------------------------------------===//
// AST Consumer Actions
//===----------------------------------------------------------------------===//

std::unique_ptr<ASTConsumer>
HTMLPrintAction::CreateASTConsumer(CompilerInstance &CI, StringRef InFile) {
  if (raw_ostream *OS = CI.createDefaultOutputFile(false, InFile))
    return CreateHTMLPrinter(OS, CI.getPreprocessor());
  return nullptr;
}

FixItAction::FixItAction() {}
FixItAction::~FixItAction() {}

std::unique_ptr<ASTConsumer>
FixItAction::CreateASTConsumer(CompilerInstance &CI, StringRef InFile) {
  return llvm::make_unique<ASTConsumer>();
}

namespace {
class FixItRewriteInPlace : public FixItOptions {
public:
  FixItRewriteInPlace() { InPlace = true; }

  std::string RewriteFilename(const std::string &Filename, int &fd) override {
    llvm_unreachable("don't call RewriteFilename for inplace rewrites");
  }
};

class FixItActionSuffixInserter : public FixItOptions {
  std::string NewSuffix;

public:
  FixItActionSuffixInserter(std::string NewSuffix, bool FixWhatYouCan)
    : NewSuffix(NewSuffix) {
      this->FixWhatYouCan = FixWhatYouCan;
  }

  std::string RewriteFilename(const std::string &Filename, int &fd) override {
    fd = -1;
    SmallString<128> Path(Filename);
    llvm::sys::path::replace_extension(Path,
      NewSuffix + llvm::sys::path::extension(Path));
    return Path.str();
  }
};

class FixItRewriteToTemp : public FixItOptions {
public:
  std::string RewriteFilename(const std::string &Filename, int &fd) override {
    SmallString<128> Path;
    llvm::sys::fs::createTemporaryFile(llvm::sys::path::filename(Filename),
                                       llvm::sys::path::extension(Filename).drop_front(), fd,
                                       Path);
    return Path.str();
  }
};
} // end anonymous namespace

bool FixItAction::BeginSourceFileAction(CompilerInstance &CI,
                                        StringRef Filename) {
  const FrontendOptions &FEOpts = getCompilerInstance().getFrontendOpts();
  if (!FEOpts.FixItSuffix.empty()) {
    FixItOpts.reset(new FixItActionSuffixInserter(FEOpts.FixItSuffix,
                                                  FEOpts.FixWhatYouCan));
  } else {
    FixItOpts.reset(new FixItRewriteInPlace);
    FixItOpts->FixWhatYouCan = FEOpts.FixWhatYouCan;
  }
  Rewriter.reset(new FixItRewriter(CI.getDiagnostics(), CI.getSourceManager(),
                                   CI.getLangOpts(), FixItOpts.get()));
  return true;
}

void FixItAction::EndSourceFileAction() {
  // Otherwise rewrite all files.
  Rewriter->WriteFixedFiles();
}

bool FixItRecompile::BeginInvocation(CompilerInstance &CI) {

  std::vector<std::pair<std::string, std::string> > RewrittenFiles;
  bool err = false;
  {
    const FrontendOptions &FEOpts = CI.getFrontendOpts();
    std::unique_ptr<FrontendAction> FixAction(new SyntaxOnlyAction());
    if (FixAction->BeginSourceFile(CI, FEOpts.Inputs[0])) {
      std::unique_ptr<FixItOptions> FixItOpts;
      if (FEOpts.FixToTemporaries)
        FixItOpts.reset(new FixItRewriteToTemp());
      else
        FixItOpts.reset(new FixItRewriteInPlace());
      FixItOpts->Silent = true;
      FixItOpts->FixWhatYouCan = FEOpts.FixWhatYouCan;
      FixItOpts->FixOnlyWarnings = FEOpts.FixOnlyWarnings;
      FixItRewriter Rewriter(CI.getDiagnostics(), CI.getSourceManager(),
                             CI.getLangOpts(), FixItOpts.get());
      FixAction->Execute();

      err = Rewriter.WriteFixedFiles(&RewrittenFiles);

      FixAction->EndSourceFile();
      CI.setSourceManager(nullptr);
      CI.setFileManager(nullptr);
    } else {
      err = true;
    }
  }
  if (err)
    return false;
  CI.getDiagnosticClient().clear();
  CI.getDiagnostics().Reset();

  PreprocessorOptions &PPOpts = CI.getPreprocessorOpts();
  PPOpts.RemappedFiles.insert(PPOpts.RemappedFiles.end(),
                              RewrittenFiles.begin(), RewrittenFiles.end());
  PPOpts.RemappedFilesKeepOriginalName = false;

  return true;
}

class InjectTestSeamVisitor
  : public RecursiveASTVisitor<InjectTestSeamVisitor> {
public:
  InjectTestSeamVisitor(Rewriter &R, ASTContext &AC)
    : _Rewriter(R), _ASTContext(AC) {}

  bool VisitFunctionDecl (FunctionDecl *FD) {
    if(FD->hasAttr<EasyTestSeamAttr>()) {
      if(!FD->isThisDeclarationADefinition()) {
        // Turn the function prototype into a variable. Example:
        // int foo(void); --> extern int (*foo)(void);
        _Rewriter.InsertText(FD->getTypeSpecStartLoc(), "extern ");
        _Rewriter.InsertTextAfterToken(FD->getNameInfo().getLocEnd(), ")");
        _Rewriter.InsertText(FD->getNameInfo().getLocStart(), "(*");
        // We have to remove the attribute, since this is no longer a
        // functionDecl
        for (Attr* At : FD->attrs()) {
          if(At->getKind() == attr::Kind::EasyTestSeam) {
            unsigned length = Lexer::MeasureTokenLength(At->getLocation(),
              _ASTContext.getSourceManager(), _ASTContext.getLangOpts());
            _Rewriter.RemoveText(At->getLocation(), length);
          }
        }
      } else {
        DeclarationNameInfo DNI = FD->getNameInfo();
        // Rename the original function. Example:
        // int foo(void) --> int _ETS_orig_foo(void)
        _Rewriter.InsertText(DNI.getLocStart(), "_ETS_orig_");

        // Reconstruct the functionDecl into a variable and assign the
        // renamed function. Example:
        // int (*foo)(void) = _ETS_orig_foo;
        std::string function_name = DNI.getName().getAsString();
        std::string funtion_return_type = FD->getReturnType().getAsString();

        std::ostringstream assignment;
        assignment << funtion_return_type << " (*" << function_name << ")(";

        bool first = true;
        for (auto PVDecl : FD->params()) {
          if (!first) assignment << ", ";
          first = false;
          assignment << PVDecl->getType().getAsString() << " " <<
                        PVDecl->getName().str();
        }
        if(first) {
          assignment << "void"; // There was no parameter
        } else if(FD->isVariadic()) {
          assignment << ", ...";
        }
        assignment << ") = _ETS_orig_" << function_name << ";";

        _Rewriter.InsertTextAfterToken(FD->getLocEnd(), assignment.str());
      }
    }
    return true;
  }
private:
  Rewriter &_Rewriter;
  ASTContext &_ASTContext;
};

class InjectTestSeamConsumer : public ASTConsumer {
public:
  InjectTestSeamConsumer(Rewriter &R, ASTContext &AC) : Visitor(R, AC) {}

  void HandleTranslationUnit(ASTContext &Context) {
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());
  }
private:
  InjectTestSeamVisitor Visitor;
};

class InjectTestSeamAction : public ASTFrontendAction {
public:
  InjectTestSeamAction(Rewriter &R) : _Rewriter(R) {}
protected:
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 StringRef InFile) {
    _Rewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return std::unique_ptr<clang::ASTConsumer>(
      new InjectTestSeamConsumer(_Rewriter, CI.getASTContext()));
  }
private:
  Rewriter &_Rewriter;
};

bool InjectTestSeamRecompile::BeginInvocation(CompilerInstance &CI) {
  Rewriter rewriter;
  std::vector<std::pair<std::string, llvm::MemoryBuffer *>> RemappedFileBuffers;
  bool err = false;
  {
    const FrontendOptions &FEOpts = CI.getFrontendOpts();

    std::unique_ptr<FrontendAction> InjectAction(new InjectTestSeamAction(rewriter));
    if (InjectAction->BeginSourceFile(CI, FEOpts.Inputs[0])) {
      // Emitting diagnostics now is not needed, the AST is reparsed after this wrapped action
      CI.getDiagnostics().setSuppressAllDiagnostics(true);
      InjectAction->Execute();
      CI.getDiagnostics().setSuppressAllDiagnostics(false);

      PreprocessorOptions &PPOpts = CI.getPreprocessorOpts();
      for (Rewriter::buffer_iterator
            I = rewriter.buffer_begin(), E = rewriter.buffer_end(); I != E; ++I) {
        FileID FID = I->first;
        RewriteBuffer &RewriteBuf = I->second;

        const FileEntry *file = CI.getSourceManager().getFileEntryForID(FID);
        assert(file);
        std::string name_of_file = file->getName();

        std::unique_ptr<llvm::MemoryBuffer> MB =
             llvm::MemoryBuffer::getMemBufferCopy(
               std::string(RewriteBuf.begin(), RewriteBuf.end()));

        PPOpts.addRemappedFile(name_of_file, MB.release());
      }

      InjectAction->EndSourceFile();
      CI.setSourceManager(nullptr);
      CI.setFileManager(nullptr);
    } else {
      err = true;
    }
  }
  if (err)
    return false;
  CI.getDiagnosticClient().clear();
  CI.getDiagnostics().Reset();
  ProcessWarningOptions(CI.getDiagnostics(), CI.getDiagnosticOpts());

  return true;
}

#ifdef CLANG_ENABLE_OBJC_REWRITER

std::unique_ptr<ASTConsumer>
RewriteObjCAction::CreateASTConsumer(CompilerInstance &CI, StringRef InFile) {
  if (raw_ostream *OS = CI.createDefaultOutputFile(false, InFile, "cpp")) {
    if (CI.getLangOpts().ObjCRuntime.isNonFragile())
      return CreateModernObjCRewriter(InFile, OS,
                                CI.getDiagnostics(), CI.getLangOpts(),
                                CI.getDiagnosticOpts().NoRewriteMacros,
                                (CI.getCodeGenOpts().getDebugInfo() !=
                                 CodeGenOptions::NoDebugInfo));
    return CreateObjCRewriter(InFile, OS,
                              CI.getDiagnostics(), CI.getLangOpts(),
                              CI.getDiagnosticOpts().NoRewriteMacros);
  }
  return nullptr;
}

#endif

//===----------------------------------------------------------------------===//
// Preprocessor Actions
//===----------------------------------------------------------------------===//

void RewriteMacrosAction::ExecuteAction() {
  CompilerInstance &CI = getCompilerInstance();
  raw_ostream *OS = CI.createDefaultOutputFile(true, getCurrentFile());
  if (!OS) return;

  RewriteMacrosInInput(CI.getPreprocessor(), OS);
}

void RewriteTestAction::ExecuteAction() {
  CompilerInstance &CI = getCompilerInstance();
  raw_ostream *OS = CI.createDefaultOutputFile(false, getCurrentFile());
  if (!OS) return;

  DoRewriteTest(CI.getPreprocessor(), OS);
}

void RewriteIncludesAction::ExecuteAction() {
  CompilerInstance &CI = getCompilerInstance();
  raw_ostream *OS = CI.createDefaultOutputFile(true, getCurrentFile());
  if (!OS) return;

  RewriteIncludesInInput(CI.getPreprocessor(), OS,
                         CI.getPreprocessorOutputOpts());
}
