; At -O1 and above on aarch64, Apple clang 21 returns from a tailcc function
; whose arguments overflow the registers without popping them, and the caller
; crashes (SIGBUS around depth 10). @stack_loop passes ten integers, more than
; aarch64's eight argument registers; @register_loop keeps its arguments in
; registers and is correct at every level. goat_llvm passes arguments past the
; register budget through the instance's spill area whether or not the local
; clang is fixed.
@fmt = private constant [6 x i8] c"%lld\0A\00"
declare i32 @printf(ptr, ...)

@stack_code = global ptr @stack_loop
define tailcc i64 @stack_loop(ptr %env, i64 %n, i64 %acc, i64 %a, i64 %b, i64 %c, i64 %d, i64 %e, i64 %f, i64 %g) {
  %z = icmp eq i64 %n, 0
  br i1 %z, label %done, label %rec
done:
  ret i64 %acc
rec:
  %m = sub i64 %n, 1
  %acc2 = add i64 %acc, %g
  %fp = load ptr, ptr @stack_code
  %r = musttail call tailcc i64 %fp(ptr %env, i64 %m, i64 %acc2, i64 %a, i64 %b, i64 %c, i64 %d, i64 %e, i64 %f, i64 %g)
  ret i64 %r
}

@register_code = global ptr @register_loop
define tailcc i64 @register_loop(ptr %env, i64 %n, i64 %acc, i64 %g) {
  %z = icmp eq i64 %n, 0
  br i1 %z, label %done, label %rec
done:
  ret i64 %acc
rec:
  %m = sub i64 %n, 1
  %acc2 = add i64 %acc, %g
  %fp = load ptr, ptr @register_code
  %r = musttail call tailcc i64 %fp(ptr %env, i64 %m, i64 %acc2, i64 %g)
  ret i64 %r
}

; Runs stack_loop when there are no arguments, register_loop otherwise.
define i32 @main(i32 %argc, ptr %argv) {
  %stack = icmp eq i32 %argc, 1
  br i1 %stack, label %with_stack, label %with_registers
with_stack:
  %s = call tailcc i64 @stack_loop(ptr null, i64 1000, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 1)
  call i32 (ptr, ...) @printf(ptr @fmt, i64 %s)
  ret i32 0
with_registers:
  %r = call tailcc i64 @register_loop(ptr null, i64 1000, i64 0, i64 1)
  call i32 (ptr, ...) @printf(ptr @fmt, i64 %r)
  ret i32 0
}
