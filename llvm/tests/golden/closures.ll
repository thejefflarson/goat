; goat native backend: textual LLVM IR

%goat_host = type { i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
%goat_instance = type { i32, i32, i32, i32, i32, ptr, i64, ptr, ptr, [8 x i64], i64, i64, [55 x ptr] }
%goat_value = type { i32, i64, i64 }

declare i32 @llvm.ctlz.i32(i32, i1)
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)
declare { i64, i1 } @llvm.smul.with.overflow.i64(i64, i64)

@goat.text.0 = private unnamed_addr constant [23 x i8] c"this number got too big"
@goat.text.1 = private unnamed_addr constant [31 x i8] c"a heap block was released twice"
@goat.text.2 = private unnamed_addr constant [29 x i8] c"the program ran out of memory"
@goat.text.3 = private unnamed_addr constant [33 x i8] c"a freed heap block was written to"

%goat.c2 = type { i32, i32, i32, i32, i64, i64 }
%goat.r2 = type { i32, i32, i64, i64 }

@goat.static.0 = private unnamed_addr constant { i32, i32, i32, i32, i64 } { i32 -1, i32 0, i32 0, i32 0, i64 ptrtoint (ptr @goat_f1 to i64) }
define tailcc i64 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = call ptr @goat.alloc(ptr %inst, i32 ptrtoint (ptr getelementptr (%goat.c2, ptr null, i32 1) to i32))
  %v2 = getelementptr inbounds i8, ptr %v1, i64 8
  store i32 0, ptr %v2
  %v3 = getelementptr inbounds i8, ptr %v1, i64 16
  store i64 ptrtoint (ptr @goat_f2 to i64), ptr %v3
  %v4 = getelementptr inbounds %goat.c2, ptr %v1, i32 0, i32 5
  store i64 10, ptr %v4
  %v5 = call ptr @goat.alloc(ptr %inst, i32 ptrtoint (ptr getelementptr (%goat.r2, ptr null, i32 1) to i32))
  %v6 = getelementptr inbounds %goat.r2, ptr %v5, i32 0, i32 2
  %v7 = ptrtoint ptr @goat.static.0 to i64
  store i64 %v7, ptr %v6
  %v8 = getelementptr inbounds %goat.r2, ptr %v5, i32 0, i32 3
  %v9 = ptrtoint ptr %v1 to i64
  store i64 %v9, ptr %v8
  %v10 = getelementptr inbounds %goat.r2, ptr %v5, i32 0, i32 2
  %v11 = load i64, ptr %v10
  %v12 = inttoptr i64 %v11 to ptr
  call void @goat.retain(ptr %v12)
  %v13 = getelementptr inbounds i8, ptr %v12, i64 16
  %v14 = load i64, ptr %v13
  %v15 = inttoptr i64 %v14 to ptr
  %v16 = call tailcc i64 %v15(ptr %inst, ptr %v12, i64 7)
  %v17 = getelementptr inbounds %goat.r2, ptr %v5, i32 0, i32 3
  %v18 = load i64, ptr %v17
  %v19 = inttoptr i64 %v18 to ptr
  call void @goat.retain(ptr %v19)
  %v20 = getelementptr inbounds i8, ptr %v19, i64 16
  %v21 = load i64, ptr %v20
  %v22 = inttoptr i64 %v21 to ptr
  %v23 = call tailcc i64 %v22(ptr %inst, ptr %v19, i64 %v16)
  call void @goat.release(ptr %inst, ptr %v5, i32 1)
  ret i64 %v23
}

define internal tailcc i64 @goat_f1(ptr %inst, ptr %env, i64 %l0) nounwind {
entry:
  %v1 = getelementptr inbounds i8, ptr %env, i64 8
  %v2 = load i32, ptr %v1
  call void @goat.release(ptr %inst, ptr %env, i32 %v2)
  %v3 = call { i64, i1 } @llvm.smul.with.overflow.i64(i64 %l0, i64 2)
  %v4 = extractvalue { i64, i1 } %v3, 1
  br i1 %v4, label %trap5, label %go6
trap5:
  %v7 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v8 = load ptr, ptr %v7
  %v9 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v10 = load ptr, ptr %v9
  %v11 = getelementptr inbounds %goat_host, ptr %v8, i32 0, i32 9
  %v12 = load ptr, ptr %v11
  call void %v12(ptr %v10, ptr @goat.text.0, i64 23) noreturn nounwind
  unreachable
go6:
  %v13 = extractvalue { i64, i1 } %v3, 0
  ret i64 %v13
}

define internal tailcc i64 @goat_f2(ptr %inst, ptr %env, i64 %l0) nounwind {
entry:
  %v1 = getelementptr inbounds %goat.c2, ptr %env, i32 0, i32 5
  %v2 = load i64, ptr %v1
  %v3 = getelementptr inbounds i8, ptr %env, i64 8
  %v4 = load i32, ptr %v3
  call void @goat.release(ptr %inst, ptr %env, i32 %v4)
  %v5 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %l0, i64 %v2)
  %v6 = extractvalue { i64, i1 } %v5, 1
  br i1 %v6, label %trap7, label %go8
trap7:
  %v9 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v10 = load ptr, ptr %v9
  %v11 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v12 = load ptr, ptr %v11
  %v13 = getelementptr inbounds %goat_host, ptr %v10, i32 0, i32 9
  %v14 = load ptr, ptr %v13
  call void %v14(ptr %v12, ptr @goat.text.0, i64 23) noreturn nounwind
  unreachable
go8:
  %v15 = extractvalue { i64, i1 } %v5, 0
  ret i64 %v15
}

define i32 @goat_main(ptr %host, ptr %ctx, ptr %inst) nounwind {
entry:
  %host_version = load i32, ptr %host
  %host_old = icmp ult i32 %host_version, 1
  br i1 %host_old, label %bad_host, label %check_instance
bad_host:
  ret i32 1
check_instance:
  %instance_version = load i32, ptr %inst
  %instance_old = icmp ult i32 %instance_version, 2
  br i1 %instance_old, label %bad_instance, label %run
bad_instance:
  ret i32 2
run:
  %host_slot = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  store ptr %host, ptr %host_slot
  %ctx_slot = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  store ptr %ctx, ptr %ctx_slot
  %v = call tailcc i64 @goat_entry(ptr %inst)
  %print_slot = getelementptr inbounds %goat_host, ptr %host, i32 0, i32 3
  %print = load ptr, ptr %print_slot
  call void %print(ptr %ctx, i64 %v) nounwind
  ret i32 0
}
define internal i32 @goat.drop.1(ptr %inst, ptr %object, i32 %pending) nounwind {
entry:
  %heap.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 5
  %heap = load ptr, ptr %heap.at
  %word1.at = getelementptr inbounds %goat.r2, ptr %object, i32 0, i32 2
  %word1 = load i64, ptr %word1.at
  %child1 = inttoptr i64 %word1 to ptr
  %rc1 = load i32, ptr %child1
  %immortal1 = icmp eq i32 %rc1, -1
  br i1 %immortal1, label %join1, label %live1
live1:
  %freed1 = icmp eq i32 %rc1, 0
  br i1 %freed1, label %twice1, label %dec1
twice1:
  %host.twice1.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %host.twice1 = load ptr, ptr %host.twice1.at
  %ctx.twice1.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %ctx.twice1 = load ptr, ptr %ctx.twice1.at
  %trap.twice1.at = getelementptr inbounds %goat_host, ptr %host.twice1, i32 0, i32 9
  %trap.twice1 = load ptr, ptr %trap.twice1.at
  call void %trap.twice1(ptr %ctx.twice1, ptr @goat.text.1, i64 31) noreturn nounwind
  unreachable
dec1:
  %n1 = sub i32 %rc1, 1
  store i32 %n1, ptr %child1
  %dead1 = icmp eq i32 %n1, 0
  br i1 %dead1, label %push1, label %join1
push1:
  store i32 %pending, ptr %child1
  %cid1.at = getelementptr inbounds i8, ptr %child1, i64 8
  %cid1 = load i32, ptr %cid1.at
  %shifted1 = shl i32 %cid1, 8
  %pad1.at = getelementptr inbounds i8, ptr %child1, i64 4
  %pad1 = load i32, ptr %pad1.at
  %tagged1 = or i32 %pad1, %shifted1
  store i32 %tagged1, ptr %pad1.at
  %at1 = ptrtoint ptr %child1 to i64
  %base1 = ptrtoint ptr %heap to i64
  %away1 = sub i64 %at1, %base1
  %scaled1 = lshr i64 %away1, 3
  %link1 = trunc i64 %scaled1 to i32
  br label %join1
join1:
  %pending1 = phi i32 [ %pending, %entry ], [ %pending, %dec1 ], [ %link1, %push1 ]
  %word2.at = getelementptr inbounds %goat.r2, ptr %object, i32 0, i32 3
  %word2 = load i64, ptr %word2.at
  %child2 = inttoptr i64 %word2 to ptr
  %rc2 = load i32, ptr %child2
  %immortal2 = icmp eq i32 %rc2, -1
  br i1 %immortal2, label %join2, label %live2
live2:
  %freed2 = icmp eq i32 %rc2, 0
  br i1 %freed2, label %twice2, label %dec2
twice2:
  %host.twice2.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %host.twice2 = load ptr, ptr %host.twice2.at
  %ctx.twice2.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %ctx.twice2 = load ptr, ptr %ctx.twice2.at
  %trap.twice2.at = getelementptr inbounds %goat_host, ptr %host.twice2, i32 0, i32 9
  %trap.twice2 = load ptr, ptr %trap.twice2.at
  call void %trap.twice2(ptr %ctx.twice2, ptr @goat.text.1, i64 31) noreturn nounwind
  unreachable
dec2:
  %n2 = sub i32 %rc2, 1
  store i32 %n2, ptr %child2
  %dead2 = icmp eq i32 %n2, 0
  br i1 %dead2, label %push2, label %join2
push2:
  store i32 %pending1, ptr %child2
  %cid2.at = getelementptr inbounds i8, ptr %child2, i64 8
  %cid2 = load i32, ptr %cid2.at
  %shifted2 = shl i32 %cid2, 8
  %pad2.at = getelementptr inbounds i8, ptr %child2, i64 4
  %pad2 = load i32, ptr %pad2.at
  %tagged2 = or i32 %pad2, %shifted2
  store i32 %tagged2, ptr %pad2.at
  %at2 = ptrtoint ptr %child2 to i64
  %base2 = ptrtoint ptr %heap to i64
  %away2 = sub i64 %at2, %base2
  %scaled2 = lshr i64 %away2, 3
  %link2 = trunc i64 %scaled2 to i32
  br label %join2
join2:
  %pending2 = phi i32 [ %pending1, %join1 ], [ %pending1, %dec2 ], [ %link2, %push2 ]
  ret i32 %pending2
}

define internal i32 @goat.class_bytes(i32 %class) nounwind alwaysinline {
  %small = icmp ule i32 %class, 32
  %by_small = shl i32 %class, 3
  %shift = sub i32 %class, 24
  %by_large = shl i32 1, %shift
  %bytes = select i1 %small, i32 %by_small, i32 %by_large
  ret i32 %bytes
}

define internal ptr @goat.alloc(ptr %inst, i32 %size) nounwind {
entry:
  %too_big = icmp ugt i32 %size, 1073741824
  br i1 %too_big, label %exhausted, label %sized
exhausted:
  %host.full.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %host.full = load ptr, ptr %host.full.at
  %ctx.full.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %ctx.full = load ptr, ptr %ctx.full.at
  %trap.full.at = getelementptr inbounds %goat_host, ptr %host.full, i32 0, i32 9
  %trap.full = load ptr, ptr %trap.full.at
  call void %trap.full(ptr %ctx.full, ptr @goat.text.2, i64 29) noreturn nounwind
  unreachable
sized:
  %rounded = add i32 %size, 7
  %aligned = and i32 %rounded, -8
  %tiny = icmp ult i32 %aligned, 16
  %bytes = select i1 %tiny, i32 16, i32 %aligned
  %is_small = icmp ule i32 %bytes, 256
  %small_class = lshr i32 %bytes, 3
  %below = sub i32 %bytes, 1
  %zeros = call i32 @llvm.ctlz.i32(i32 %below, i1 false)
  %large_class = sub i32 56, %zeros
  %class = select i1 %is_small, i32 %small_class, i32 %large_class
  %block_bytes = call i32 @goat.class_bytes(i32 %class)
  %head.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 12, i32 %class
  %head = load ptr, ptr %head.at
  %has_free = icmp ne ptr %head, null
  br i1 %has_free, label %pop, label %bump
pop:
  %head_rc = load i32, ptr %head
  %written = icmp ne i32 %head_rc, 0
  br i1 %written, label %corrupt, label %unlink
corrupt:
  %host.stale.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %host.stale = load ptr, ptr %host.stale.at
  %ctx.stale.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %ctx.stale = load ptr, ptr %ctx.stale.at
  %trap.stale.at = getelementptr inbounds %goat_host, ptr %host.stale, i32 0, i32 9
  %trap.stale = load ptr, ptr %trap.stale.at
  call void %trap.stale(ptr %ctx.stale, ptr @goat.text.3, i64 33) noreturn nounwind
  unreachable
unlink:
  %link.at = getelementptr inbounds i8, ptr %head, i64 8
  %next = load ptr, ptr %link.at
  store ptr %next, ptr %head.at
  br label %ready
bump:
  %top.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 10
  %top0 = load i64, ptr %top.at
  %fresh = icmp ult i64 %top0, 16
  %top = select i1 %fresh, i64 16, i64 %top0
  %span = zext i32 %block_bytes to i64
  %end = add i64 %top, %span
  %limit.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 6
  %limit = load i64, ptr %limit.at
  %past = icmp ugt i64 %end, %limit
  br i1 %past, label %full, label %take
full:
  %host.over.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %host.over = load ptr, ptr %host.over.at
  %ctx.over.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %ctx.over = load ptr, ptr %ctx.over.at
  %trap.over.at = getelementptr inbounds %goat_host, ptr %host.over, i32 0, i32 9
  %trap.over = load ptr, ptr %trap.over.at
  call void %trap.over(ptr %ctx.over, ptr @goat.text.2, i64 29) noreturn nounwind
  unreachable
take:
  store i64 %end, ptr %top.at
  %heap.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 5
  %heap = load ptr, ptr %heap.at
  %fresh_block = getelementptr inbounds i8, ptr %heap, i64 %top
  br label %ready
ready:
  %block = phi ptr [ %head, %unlink ], [ %fresh_block, %take ]
  store i32 1, ptr %block
  %class.at = getelementptr inbounds i8, ptr %block, i64 4
  store i32 %class, ptr %class.at
  %live.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 1
  %live = load i32, ptr %live.at
  %live1 = add i32 %live, 1
  store i32 %live1, ptr %live.at
  %count.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 11
  %count = load i64, ptr %count.at
  %count1 = add i64 %count, 1
  store i64 %count1, ptr %count.at
  ret ptr %block
}

define internal void @goat.free(ptr %inst, ptr %block) nounwind {
entry:
  %rc = load i32, ptr %block
  %held = icmp ne i32 %rc, 0
  br i1 %held, label %twice, label %go
twice:
  %host.twice.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %host.twice = load ptr, ptr %host.twice.at
  %ctx.twice.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %ctx.twice = load ptr, ptr %ctx.twice.at
  %trap.twice.at = getelementptr inbounds %goat_host, ptr %host.twice, i32 0, i32 9
  %trap.twice = load ptr, ptr %trap.twice.at
  call void %trap.twice(ptr %ctx.twice, ptr @goat.text.1, i64 31) noreturn nounwind
  unreachable
go:
  %class.at = getelementptr inbounds i8, ptr %block, i64 4
  %class = load i32, ptr %class.at
  %bytes = call i32 @goat.class_bytes(i32 %class)
  %payload = getelementptr inbounds i8, ptr %block, i64 8
  %rest = sub i32 %bytes, 8
  %rest64 = zext i32 %rest to i64
  call void @llvm.memset.p0.i64(ptr %payload, i8 -2, i64 %rest64, i1 false)
  %head.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 12, i32 %class
  %head = load ptr, ptr %head.at
  %link.at = getelementptr inbounds i8, ptr %block, i64 8
  store ptr %head, ptr %link.at
  store ptr %block, ptr %head.at
  %live.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 1
  %live = load i32, ptr %live.at
  %live1 = sub i32 %live, 1
  store i32 %live1, ptr %live.at
  ret void
}

define internal void @goat.drop_loop(ptr %inst, ptr %first, i32 %first_id) nounwind {
entry:
  br label %loop
loop:
  %object = phi ptr [ %first, %entry ], [ %next, %pop ]
  %id = phi i32 [ %first_id, %entry ], [ %next_id, %pop ]
  %pending = phi i32 [ 0, %entry ], [ %link, %pop ]
  switch i32 %id, label %leaf [ i32 1, label %drop1 ]
leaf:
  br label %release
drop1:
  %after1 = call i32 @goat.drop.1(ptr %inst, ptr %object, i32 %pending)
  br label %release
release:
  %remaining = phi i32 [ %pending, %leaf ], [ %after1, %drop1 ]
  call void @goat.free(ptr %inst, ptr %object)
  %empty = icmp eq i32 %remaining, 0
  br i1 %empty, label %done, label %pop
pop:
  %heap.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 5
  %heap = load ptr, ptr %heap.at
  %scaled = zext i32 %remaining to i64
  %offset = shl i64 %scaled, 3
  %next = getelementptr inbounds i8, ptr %heap, i64 %offset
  %link = load i32, ptr %next
  store i32 0, ptr %next
  %pad.at = getelementptr inbounds i8, ptr %next, i64 4
  %pad = load i32, ptr %pad.at
  %next_id = lshr i32 %pad, 8
  %class = and i32 %pad, 255
  store i32 %class, ptr %pad.at
  br label %loop
done:
  ret void
}

define internal void @goat.retain(ptr %p) nounwind alwaysinline {
  %rc = load i32, ptr %p
  %immortal = icmp eq i32 %rc, -1
  br i1 %immortal, label %done, label %inc
inc:
  %n = add i32 %rc, 1
  store i32 %n, ptr %p
  br label %done
done:
  ret void
}

define internal void @goat.release(ptr %inst, ptr %p, i32 %id) nounwind alwaysinline {
entry:
  %rc = load i32, ptr %p
  %immortal = icmp eq i32 %rc, -1
  br i1 %immortal, label %done, label %live
live:
  %freed = icmp eq i32 %rc, 0
  br i1 %freed, label %twice, label %dec
twice:
  %host.twice.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %host.twice = load ptr, ptr %host.twice.at
  %ctx.twice.at = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %ctx.twice = load ptr, ptr %ctx.twice.at
  %trap.twice.at = getelementptr inbounds %goat_host, ptr %host.twice, i32 0, i32 9
  %trap.twice = load ptr, ptr %trap.twice.at
  call void %trap.twice(ptr %ctx.twice, ptr @goat.text.1, i64 31) noreturn nounwind
  unreachable
dec:
  %n = sub i32 %rc, 1
  store i32 %n, ptr %p
  %dead = icmp eq i32 %n, 0
  br i1 %dead, label %drop, label %done
drop:
  call void @goat.drop_loop(ptr %inst, ptr %p, i32 %id)
  br label %done
done:
  ret void
}

