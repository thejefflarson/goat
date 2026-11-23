; goat native backend: textual LLVM IR

declare void @goat_trap(ptr, ptr, i32) noreturn nounwind
declare double @llvm.sqrt.f64(double)
declare double @llvm.trunc.f64(double)

@goat.trap.0 = private unnamed_addr constant [40 x i8] c"this number can't be made a whole number"

define i64 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = sitofp i64 17 to double
  %v2 = call double @llvm.sqrt.f64(double %v1)
  %v3 = call double @llvm.trunc.f64(double %v2)
  %v4 = fcmp oge double %v3, 0xC3E0000000000000
  %v5 = fcmp olt double %v3, 0x43E0000000000000
  %v6 = and i1 %v4, %v5
  %v7 = xor i1 %v6, true
  br i1 %v7, label %trap8, label %go9
trap8:
  call void @goat_trap(ptr %inst, ptr @goat.trap.0, i32 40)
  unreachable
go9:
  %v10 = fptosi double %v3 to i64
  ret i64 %v10
}

