(module
  (type (;0;) (func (param f64)))
  (type (;1;) (func (param i32)))
  (type (;2;) (func))
  (type (;3;) (func (result f64)))
  (type (;4;) (func (param i32) (result f64)))
  (type (;5;) (func (param i32) (result i32)))
  (type (;6;) (func (result i32)))
  (type (;7;) (func (param i32 i32)))
  (type (;8;) (func (param i32 i32) (result i32)))
  (import "goat" "print_number" (func (;0;) (type 0) (param f64)))
  (import "goat" "print_bool" (func (;1;) (type 1) (param i32)))
  (table (;0;) 1 1 funcref)
  (memory (;0;) 1)
  (global (;0;) (mut i32) i32.const 248)
  (global (;1;) (mut i32) i32.const 0)
  (export "memory" (memory 0))
  (export "goat_entry" (func 4))
  (export "goat_alloc" (func 5))
  (export "goat_live_allocs" (func 7))
  (elem (;0;) (table 0) (i32.const 0) func 9)
  (func (;2;) (type 3) (result f64)
    (local f64 i32 i32)
    f64.const 0x1p+0 (;=1;)
    local.set 0
    i32.const 8
    local.set 1
    i32.const 32
    call 5
    local.set 2
    local.get 2
    i32.const 1
    i32.store offset=8
    local.get 2
    local.get 0
    f64.store offset=16
    local.get 2
    local.get 1
    i32.store offset=24
    local.get 2
    return_call 3
  )
  (func (;3;) (type 4) (param i32) (result f64)
    (local f64 i32 i32)
    block (result f64) ;; label = @1
      block ;; label = @2
        block ;; label = @3
          local.get 0
          i32.load offset=8
          br_table 0 (;@3;) 1 (;@2;)
        end
        local.get 0
        i32.load
        i32.const -1
        i32.ne
        if ;; label = @3
          local.get 0
          i32.load
          i32.eqz
          if ;; label = @4
            unreachable
          end
          local.get 0
          local.get 0
          i32.load
          i32.const 1
          i32.sub
          i32.store
          local.get 0
          i32.load
          i32.eqz
          if ;; label = @4
            local.get 0
            i32.const 0
            call 8
          end
        end
        f64.const 0x0p+0 (;=0;)
        br 1 (;@1;)
      end
      local.get 0
      f64.load offset=16
      local.set 1
      local.get 0
      i32.load offset=24
      local.tee 2
      local.get 2
      i32.load
      i32.const -1
      i32.ne
      if ;; label = @2
        local.get 2
        local.get 2
        i32.load
        i32.const 1
        i32.add
        i32.store
      end
      local.set 3
      local.get 0
      i32.load
      i32.const -1
      i32.ne
      if ;; label = @2
        local.get 0
        i32.load
        i32.eqz
        if ;; label = @3
          unreachable
        end
        local.get 0
        local.get 0
        i32.load
        i32.const 1
        i32.sub
        i32.store
        local.get 0
        i32.load
        i32.eqz
        if ;; label = @3
          local.get 0
          i32.const 0
          call 8
        end
      end
      f64.const 0x1p+0 (;=1;)
      local.get 3
      call 3
      f64.add
    end
  )
  (func (;4;) (type 2)
    call 2
    call 0
  )
  (func (;5;) (type 5) (param i32) (result i32)
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
    i32.load offset=24
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
      i32.store offset=24
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
    i32.load offset=24
    i32.store offset=8
    local.get 1
    i32.const 2
    i32.shl
    local.get 0
    i32.store offset=24
    global.get 1
    i32.const 1
    i32.sub
    global.set 1
  )
  (func (;7;) (type 6) (result i32)
    global.get 1
  )
  (func (;8;) (type 7) (param i32 i32)
    (local i32)
    block ;; label = @1
      loop ;; label = @2
        local.get 0
        local.get 2
        local.get 1
        call_indirect (type 8)
        local.set 2
        local.get 0
        call 6
        local.get 2
        i32.eqz
        br_if 1 (;@1;)
        local.get 2
        local.set 0
        local.get 0
        i32.load
        local.set 2
        local.get 0
        i32.const 0
        i32.store
        local.get 0
        i32.load offset=4
        i32.const 8
        i32.shr_u
        local.set 1
        local.get 0
        local.get 0
        i32.load offset=4
        i32.const 255
        i32.and
        i32.store offset=4
        br 0 (;@2;)
      end
    end
  )
  (func (;9;) (type 8) (param i32 i32) (result i32)
    (local i32)
    block ;; label = @1
      block ;; label = @2
        block ;; label = @3
          local.get 0
          i32.load offset=8
          br_table 1 (;@2;) 0 (;@3;) 1 (;@2;)
        end
        local.get 0
        i32.load offset=24
        local.set 2
        local.get 2
        i32.load
        i32.const -1
        i32.ne
        if ;; label = @3
          local.get 2
          i32.load
          i32.eqz
          if ;; label = @4
            unreachable
          end
          local.get 2
          local.get 2
          i32.load
          i32.const 1
          i32.sub
          i32.store
          local.get 2
          i32.load
          i32.eqz
          if ;; label = @4
            local.get 2
            local.get 1
            i32.store
            local.get 2
            local.get 2
            i32.load offset=4
            i32.const 0
            i32.or
            i32.store offset=4
            local.get 2
            local.set 1
          end
        end
        br 1 (;@1;)
      end
    end
    local.get 1
  )
  (data (;0;) (i32.const 8) "\ff\ff\ff\ff\00\00\00\00\00\00\00\00\00\00\00\00")
)
