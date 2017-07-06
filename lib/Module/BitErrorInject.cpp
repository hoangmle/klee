#include "Passes.h"
#include "klee/Config/Version.h"
#include "klee/Internal/Support/ErrorHandling.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/LLVMContext.h"
#else
#include "llvm/LLVMContext.h"
#endif
#include "llvm/ADT/StringSet.h"
#include "llvm/DebugInfo.h"

using namespace llvm;

namespace klee {

char BitErrorInject::ID = 0;

struct Util {
  static void replaceAllUses(Instruction *from, Instruction *to) {
    std::vector<User *> users;
    std::vector<int> operand_numbers;

    // Note: Adding instruction *from* while iterating can lead to infinite loop
    // - therefore the collection of elements
    // and the actual replacement is done in seperate steps.
    for (Value::use_iterator U = from->use_begin(); U != from->use_end(); ++U) {
      users.push_back(U.getUse().getUser());
      operand_numbers.push_back(U.getOperandNo());
    }

    for (unsigned i = 0; i < users.size(); ++i) {
      users[i]->setOperand(operand_numbers[i], to);
    }
  }
  
  static Constant *getLineNumber(Instruction *instr){
    if (MDNode *N = instr->getMetadata("dbg")) {
        DILocation Loc(N);
        unsigned line = Loc.getLineNumber();
        return ConstantInt::get(Type::getInt32Ty(instr->getContext()), line);
    } else {
      return ConstantInt::get(Type::getInt32Ty(instr->getContext()), -1);
    }
  }
};

static llvm::StringSet<> ignoreList;

bool BitErrorInject::doInitialization(Module &M) {
  MaybeBitflipFunction = M.getFunction("maybe_bitflip");
  assert(MaybeBitflipFunction);
  klee_message("found maybe_bitflip() @ %d", MaybeBitflipFunction);

  ignoreList.insert("maybe_bitflip");
  ignoreList.insert("bitflip");
  ignoreList.insert("maybe_mutate_arithmetic_operation");
  ignoreList.insert("CHECK");
  ignoreList.insert("error");
  ignoreList.insert("error_lib_initialize");
  ignoreList.insert("main");
  ignoreList.insert("start_error_injection");
  ignoreList.insert("stop_error_injection");
  ignoreList.insert("interrupt_error_injection");
  ignoreList.insert("restore_error_injection");

  return false;
}

bool BitErrorInject::processInstruction(BasicBlock *bb, Instruction *I) {
  // TODO: add more instructions here ...
  if (isa<BinaryOperator>(I) || isa<LoadInst>(I) || isa<CmpInst>(I)) {

    if (!I->getType()->isIntegerTy()) {
      klee_message("[instr] only inject bitflip for integer types");
      return false;
    }

    IntegerType *i_type = dyn_cast<IntegerType>(I->getType());
    assert(i_type);

    if (i_type->getBitWidth() > 32) {
      // Unsupported for now ... change the klee error_lib.h to support larger
      // int types
      return false;
    }

    /* Note: cannot directly add the instruction itself as argument to the call,
     * since the subsequent replacement
     * would try to replace it too. So add some dummy constant here and replace
     * it with the instruction I at the end.
     */
    ConstantInt *cons = ConstantInt::get(Type::getInt32Ty(I->getContext()), 0);
    static unsigned cnt = 0;
    ConstantInt *loc = ConstantInt::get(Type::getInt32Ty(I->getContext()), ++cnt);
    std::vector<Value *> args;
    args.push_back(cons);
    args.push_back(loc);
    args.push_back(Util::getLineNumber(I));
    Instruction *call =
        CallInst::Create(MaybeBitflipFunction, ArrayRef<Value *>(args));

    if (i_type->getBitWidth() < 32) {
      /*
                          I
              upcast:     ZExt(I)
              call:       maybe_bitflip(upcast)
              downcast:   Trunc(call)
      */
      Instruction *downcast = TruncInst::Create(
          Instruction::Trunc, call,
          IntegerType::get(I->getContext(), i_type->getBitWidth()));

      /* Put the result of the call everywhere the result of I is used. */
      Util::replaceAllUses(I, downcast);

      // Create instruction after the replaceAllUses, otherwise it seems this I
      // is replaced too
      Instruction *upcast = ZExtInst::Create(Instruction::ZExt, I,
                                             Type::getInt32Ty(I->getContext()));

      // Now use the result of I as call argument and insert the call
      // instruction after I.
      call->setOperand(0, upcast);

      // Add instructions
      bb->getInstList().insertAfter(I, upcast);
      bb->getInstList().insertAfter(upcast, call);
      bb->getInstList().insertAfter(call, downcast);
    } else {
      /* Put the result of the call everywhere the result of I is used. */
      Util::replaceAllUses(I, call);

      // Now use the result of I as call argument and insert the call
      // instruction after I.
      call->setOperand(0, I);
      bb->getInstList().insertAfter(I, call);
    }

    klee_message("[instr] added maybe bitflip");
    return true;
  }
  return false;
}

bool BitErrorInject::runOnFunction(Function &func) {
  klee_message("runOnFunction: %s", func.getName().str().c_str());

  if (ignoreList.find(func.getName()) != ignoreList.end()) {
    klee_message("  skip this function");
    return false;
  }

  if (func.getName().startswith("klee_")) {
    klee_message("  skip this instrinsic");
    return false;
  }

  bool modified = false;

  for (Function::iterator it = func.begin(); it != func.end(); ++it) {
    BasicBlock *bb = it;
    for (BasicBlock::iterator i = bb->begin(); i != bb->end(); ++i) {
      modified |= processInstruction(bb, i);
    }
  }

  return modified;
}
}
