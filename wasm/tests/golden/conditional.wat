(module
  (type (;0;) (func (param f64)))
  (type (;1;) (func (param i32)))
  (type (;2;) (func))
  (type (;3;) (func (result f64)))
  (import "goat" "print_number" (func (;0;) (type 0) (param f64)))
  (import "goat" "print_bool" (func (;1;) (type 1) (param i32)))
  (memory (;0;) 1)
  (global (;0;) (mut i32) i32.const 8)
  (export "memory" (memory 0))
  (export "goat_entry" (func 3))
  (func (;2;) (type 3) (result f64)
    (local f64)
    f64.const 0x1.8p+1 (;=3;)
    local.set 0
    local.get 0
    f64.const 0x1.4p+2 (;=5;)
    f64.lt
    if (result f64) ;; label = @1
      local.get 0
      f64.const 0x1p+0 (;=1;)
      f64.sub
    else
      unreachable
    end
  )
  (func (;3;) (type 2)
    call 2
    call 0
  )
  (data (;0;) (i32.const 8) "")
)
