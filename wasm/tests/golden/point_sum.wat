(module
  (type (;0;) (func (param f64)))
  (type (;1;) (func (param i32)))
  (type (;2;) (func))
  (type (;3;) (func (result i32)))
  (import "goat" "print_number" (func (;0;) (type 0) (param f64)))
  (import "goat" "print_bool" (func (;1;) (type 1) (param i32)))
  (memory (;0;) 1)
  (global (;0;) (mut i32) i32.const 8)
  (export "memory" (memory 0))
  (export "goat_entry" (func 3))
  (func (;2;) (type 3) (result i32)
    (local i32 i32 i32 i32 i32)
    i32.const 3
    local.set 0
    i32.const 4
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
    local.get 0
    i32.store offset=8
    local.get 2
    local.get 1
    i32.store offset=16
    local.get 2
    local.set 3
    local.get 3
    i32.load offset=8
    local.get 3
    i32.load offset=16
    i32.add
    local.set 4
    local.get 3
    i32.load
    i32.const -1
    i32.ne
    if ;; label = @1
      local.get 3
      local.get 3
      i32.load
      i32.const 1
      i32.sub
      i32.store
      local.get 3
      i32.load
      i32.eqz
      if ;; label = @2
        local.get 3
        call 4
      end
    end
    local.get 4
  )
  (func (;3;) (type 2)
    call 2
    f64.convert_i32_s
    call 0
  )
  (func (;4;) (type 1) (param i32)
    (local i32)
  )
  (data (;0;) (i32.const 8) "")
)
