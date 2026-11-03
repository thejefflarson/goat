(module
  (type (;0;) (func (param f64)))
  (type (;1;) (func (param i32)))
  (type (;2;) (func))
  (type (;3;) (func (result f64)))
  (type (;4;) (func (param f64) (result i32)))
  (type (;5;) (func (param i32 f64) (result f64)))
  (import "goat" "print_number" (func (;0;) (type 0) (param f64)))
  (import "goat" "print_bool" (func (;1;) (type 1) (param i32)))
  (table (;0;) 2 2 funcref)
  (memory (;0;) 1)
  (global (;0;) (mut i32) i32.const 8)
  (export "memory" (memory 0))
  (export "goat_entry" (func 5))
  (elem (;0;) (table 0) (i32.const 0) func 6 4)
  (func (;2;) (type 3) (result f64)
    (local i32)
    f64.const 0x1p+0 (;=1;)
    call 3
    local.set 0
    local.get 0
    f64.const 0x1p+1 (;=2;)
    local.get 0
    i32.load offset=12
    return_call_indirect (type 5)
  )
  (func (;3;) (type 4) (param f64) (result i32)
    (local f64 i32)
    local.get 0
    local.set 1
    global.get 0
    local.tee 2
    i32.const 24
    i32.add
    global.set 0
    local.get 2
    i32.const 1
    i32.store
    local.get 2
    i32.const 0
    i32.store offset=8
    local.get 2
    i32.const 1
    i32.store offset=12
    local.get 2
    local.get 1
    f64.store offset=16
    local.get 2
  )
  (func (;4;) (type 5) (param i32 f64) (result f64)
    (local f64)
    local.get 0
    f64.load offset=16
    local.get 1
    f64.add
    local.set 2
    local.get 0
    i32.load
    i32.const -1
    i32.ne
    if ;; label = @1
      local.get 0
      local.get 0
      i32.load
      i32.const 1
      i32.sub
      i32.store
      local.get 0
      i32.load
      i32.eqz
      if ;; label = @2
        local.get 0
        local.get 0
        i32.load offset=8
        call_indirect (type 1)
      end
    end
    local.get 2
  )
  (func (;5;) (type 2)
    call 2
    call 0
  )
  (func (;6;) (type 1) (param i32)
    (local i32)
  )
  (data (;0;) (i32.const 8) "")
)
