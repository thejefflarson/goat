(module
  (type (;0;) (func (param f64)))
  (type (;1;) (func (param i32)))
  (type (;2;) (func))
  (type (;3;) (func (result i32)))
  (type (;4;) (func (param i32) (result i32)))
  (import "goat" "print_number" (func (;0;) (type 0) (param f64)))
  (import "goat" "print_bool" (func (;1;) (type 1) (param i32)))
  (memory (;0;) 1)
  (global (;0;) (mut i32) i32.const 232)
  (global (;1;) (mut i32) i32.const 0)
  (global (;2;) (mut i32) i32.const 2147483647)
  (export "memory" (memory 0))
  (export "goat_entry" (func 4))
  (export "goat_fuel" (global 2))
  (export "goat_alloc" (func 5))
  (export "goat_live_allocs" (func 7))
  (func (;2;) (type 3) (result i32)
    global.get 2
    i32.const 1
    i32.sub
    global.set 2
    global.get 2
    i32.const 0
    i32.le_s
    if ;; label = @1
      unreachable
    end
    i32.const 10
    call 3
  )
  (func (;3;) (type 4) (param i32) (result i32)
    global.get 2
    i32.const 1
    i32.sub
    global.set 2
    global.get 2
    i32.const 0
    i32.le_s
    if ;; label = @1
      unreachable
    end
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
  (func (;5;) (type 4) (param i32) (result i32)
    (local i32 i32 i32 i32)
    local.get 0
    i32.const 1073741824
    i32.gt_u
    if ;; label = @1
      unreachable
    end
    local.get 0
    i32.const 7
    i32.add
    i32.const -8
    i32.and
    local.set 3
    local.get 3
    i32.const 16
    i32.lt_u
    if ;; label = @1
      i32.const 16
      local.set 3
    end
    local.get 3
    i32.const 256
    i32.le_u
    if (result i32) ;; label = @1
      local.get 3
      i32.const 3
      i32.shr_u
    else
      i32.const 56
      local.get 3
      i32.const 1
      i32.sub
      i32.clz
      i32.sub
    end
    local.set 1
    local.get 1
    i32.const 32
    i32.le_u
    if (result i32) ;; label = @1
      local.get 1
      i32.const 3
      i32.shl
    else
      i32.const 1
      local.get 1
      i32.const 24
      i32.sub
      i32.shl
    end
    local.set 3
    local.get 1
    i32.const 2
    i32.shl
    i32.load offset=8
    local.tee 2
    if ;; label = @1
      local.get 2
      i32.load
      if ;; label = @2
        unreachable
      end
      local.get 1
      i32.const 2
      i32.shl
      local.get 2
      i32.load offset=8
      i32.store offset=8
    else
      global.get 0
      local.tee 2
      local.get 3
      i32.add
      local.tee 4
      memory.size
      i32.const 16
      i32.shl
      i32.gt_u
      if ;; label = @2
        local.get 4
        memory.size
        i32.const 16
        i32.shl
        i32.sub
        i32.const 65535
        i32.add
        i32.const 16
        i32.shr_u
        memory.grow
        i32.const -1
        i32.eq
        if ;; label = @3
          unreachable
        end
      end
      local.get 4
      global.set 0
    end
    local.get 2
    i32.const 1
    i32.store
    local.get 2
    local.get 1
    i32.store offset=4
    global.get 1
    i32.const 1
    i32.add
    global.set 1
    local.get 2
  )
  (func (;6;) (type 1) (param i32)
    (local i32 i32)
    local.get 0
    i32.load
    if ;; label = @1
      unreachable
    end
    local.get 0
    i32.load offset=4
    local.set 1
    local.get 1
    i32.const 32
    i32.le_u
    if (result i32) ;; label = @1
      local.get 1
      i32.const 3
      i32.shl
    else
      i32.const 1
      local.get 1
      i32.const 24
      i32.sub
      i32.shl
    end
    local.set 2
    local.get 0
    i32.const 8
    i32.add
    i32.const 254
    local.get 2
    i32.const 8
    i32.sub
    memory.fill
    local.get 0
    local.get 1
    i32.const 2
    i32.shl
    i32.load offset=8
    i32.store offset=8
    local.get 1
    i32.const 2
    i32.shl
    local.get 0
    i32.store offset=8
    global.get 1
    i32.const 1
    i32.sub
    global.set 1
  )
  (func (;7;) (type 3) (result i32)
    global.get 1
  )
  (data (;0;) (i32.const 8) "")
)
