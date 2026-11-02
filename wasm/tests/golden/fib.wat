(module
  (type (;0;) (func (param f64)))
  (type (;1;) (func (param i32)))
  (type (;2;) (func))
  (type (;3;) (func (result i32)))
  (type (;4;) (func (param i32) (result i32)))
  (import "goat" "print_number" (func (;0;) (type 0) (param f64)))
  (import "goat" "print_bool" (func (;1;) (type 1) (param i32)))
  (memory (;0;) 1)
  (global (;0;) (mut i32) i32.const 8)
  (export "memory" (memory 0))
  (export "goat_entry" (func 4))
  (func (;2;) (type 3) (result i32)
    i32.const 10
    call 3
  )
  (func (;3;) (type 4) (param i32) (result i32)
    local.get 0
    i32.const 2
    i32.lt_s
    if (result i32) ;; label = @1
      local.get 0
    else
      local.get 0
      i32.const 1
      i32.sub
      call 3
      local.get 0
      i32.const 2
      i32.sub
      call 3
      i32.add
    end
  )
  (func (;4;) (type 2)
    call 2
    f64.convert_i32_s
    call 0
  )
  (data (;0;) (i32.const 8) "")
)
