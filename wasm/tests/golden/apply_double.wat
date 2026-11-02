(module
  (type (;0;) (func (param f64)))
  (type (;1;) (func (param i32)))
  (type (;2;) (func))
  (type (;3;) (func (result i32)))
  (type (;4;) (func (param i32 i32) (result i32)))
  (import "goat" "print_number" (func (;0;) (type 0) (param f64)))
  (import "goat" "print_bool" (func (;1;) (type 1) (param i32)))
  (table (;0;) 2 2 funcref)
  (memory (;0;) 1)
  (global (;0;) (mut i32) i32.const 24)
  (export "memory" (memory 0))
  (export "goat_entry" (func 5))
  (elem (;0;) (table 0) (i32.const 0) func 6 3)
  (func (;2;) (type 3) (result i32)
    i32.const 8
    i32.const 21
    call 4
  )
  (func (;3;) (type 4) (param i32 i32) (result i32)
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
    local.get 1
    i32.const 2
    i32.mul
  )
  (func (;4;) (type 4) (param i32 i32) (result i32)
    (local i32)
    local.get 0
    local.set 2
    local.get 2
    local.get 1
    local.get 2
    i32.load offset=12
    call_indirect (type 4)
  )
  (func (;5;) (type 2)
    call 2
    f64.convert_i32_s
    call 0
  )
  (func (;6;) (type 1) (param i32)
    (local i32)
  )
  (data (;0;) (i32.const 8) "\ff\ff\ff\ff\00\00\00\00\00\00\00\00\01\00\00\00")
)
