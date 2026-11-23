; goat native backend: textual LLVM IR

declare void @goat_trap(ptr, ptr, i32) noreturn nounwind
declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)

@goat.trap.0 = private unnamed_addr constant [23 x i8] c"this number got too big"

define i64 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = call i64 @goat_f1(ptr %inst, i64 20, i64 22)
  ret i64 %v1
}

define internal i64 @goat_f1(ptr %inst, i64 %l0, i64 %l1) nounwind {
entry:
  %v1 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %l0, i64 %l1)
  %v2 = extractvalue { i64, i1 } %v1, 1
  br i1 %v2, label %trap3, label %go4
trap3:
  call void @goat_trap(ptr %inst, ptr @goat.trap.0, i32 23)
  unreachable
go4:
  %v5 = extractvalue { i64, i1 } %v1, 0
  ret i64 %v5
}

