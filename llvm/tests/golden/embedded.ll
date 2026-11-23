; goat native backend: textual LLVM IR

declare void @goat_trap(ptr, ptr, i32) noreturn nounwind
declare { i32, i1 } @llvm.sadd.with.overflow.i32(i32, i32)
declare { i32, i1 } @llvm.smul.with.overflow.i32(i32, i32)
declare { i32, i1 } @llvm.ssub.with.overflow.i32(i32, i32)

@goat.trap.0 = private unnamed_addr constant [23 x i8] c"this number got too big"

define i32 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 2, i32 3)
  %v2 = extractvalue { i32, i1 } %v1, 1
  br i1 %v2, label %trap3, label %go4
trap3:
  call void @goat_trap(ptr %inst, ptr @goat.trap.0, i32 23)
  unreachable
go4:
  %v5 = extractvalue { i32, i1 } %v1, 0
  %v6 = call { i32, i1 } @llvm.ssub.with.overflow.i32(i32 10, i32 4)
  %v7 = extractvalue { i32, i1 } %v6, 1
  br i1 %v7, label %trap8, label %go9
trap8:
  call void @goat_trap(ptr %inst, ptr @goat.trap.0, i32 23)
  unreachable
go9:
  %v10 = extractvalue { i32, i1 } %v6, 0
  %v11 = call { i32, i1 } @llvm.smul.with.overflow.i32(i32 %v5, i32 %v10)
  %v12 = extractvalue { i32, i1 } %v11, 1
  br i1 %v12, label %trap13, label %go14
trap13:
  call void @goat_trap(ptr %inst, ptr @goat.trap.0, i32 23)
  unreachable
go14:
  %v15 = extractvalue { i32, i1 } %v11, 0
  ret i32 %v15
}

