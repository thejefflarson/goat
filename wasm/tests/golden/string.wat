(module
  (type (;0;) (func (param f64)))
  (type (;1;) (func (param i32)))
  (type (;2;) (func))
  (type (;3;) (func (result i32)))
  (import "goat" "print_number" (func (;0;) (type 0) (param f64)))
  (import "goat" "print_bool" (func (;1;) (type 1) (param i32)))
  (import "goat" "print_string" (func (;2;) (type 1) (param i32)))
  (memory (;0;) 1)
  (global (;0;) (mut i32) i32.const 24)
  (export "memory" (memory 0))
  (export "goat_entry" (func 4))
  (func (;3;) (type 3) (result i32)
    i32.const 8
  )
  (func (;4;) (type 2)
    call 3
    call 2
  )
  (data (;0;) (i32.const 8) "\ff\ff\ff\ff\00\00\00\00\02\00\00\00hi\00\00")
)
