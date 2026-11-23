; goat native backend: textual LLVM IR

declare void @goat_trap(ptr, ptr, i32) noreturn nounwind


define double @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = fadd double 0x3FF8000000000000, 0x4004000000000000
  %v2 = fmul double %v1, 0x4000000000000000
  ret double %v2
}

