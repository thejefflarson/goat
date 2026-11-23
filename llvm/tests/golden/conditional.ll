; goat native backend: textual LLVM IR

declare void @goat_trap(ptr, ptr, i32) noreturn nounwind


define double @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = fcmp olt double 0x4008000000000000, 0x4014000000000000
  br i1 %v1, label %then2, label %else3
then2:
  %v5 = fadd double 0x4008000000000000, 0x3FF0000000000000
  br label %join4
else3:
  br label %join4
join4:
  %v6 = phi double [ %v5, %then2 ], [ 0x4008000000000000, %else3 ]
  ret double %v6
}

