; goat native backend: textual LLVM IR

%goat_host = type { i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
%goat_instance = type { i32, i32, i32, i32, i32, ptr, i64, ptr, ptr, [8 x i64], i64, i64, [55 x ptr] }
%goat_value = type { i32, i64, i64 }

declare i32 @llvm.ctlz.i32(i32, i1)
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)

@goat.text.0 = private unnamed_addr constant [23 x i8] c"this number got too big"
@goat.text.1 = private unnamed_addr constant [29 x i8] c"the program ran out of memory"
@goat.text.2 = private unnamed_addr constant [33 x i8] c"a freed heap block was written to"
@goat.text.3 = private unnamed_addr constant [31 x i8] c"a heap block was released twice"

%goat.r0 = type { i32, i32, i64 }
%goat.v1.t1 = type { i32, i32, i32, i32, i64 }

define tailcc i64 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 40, i64 0)
  %v2 = extractvalue { i64, i1 } %v1, 1
  br i1 %v2, label %trap3, label %go4
trap3:
  %v5 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v6 = load ptr, ptr %v5
  %v7 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v8 = load ptr, ptr %v7
  %v9 = getelementptr inbounds %goat_host, ptr %v6, i32 0, i32 9
  %v10 = load ptr, ptr %v9
  call void %v10(ptr %v8, ptr @goat.text.0, i64 23) noreturn nounwind
  unreachable
go4:
  %v11 = extractvalue { i64, i1 } %v1, 0
  %v12 = call ptr @goat.alloc(ptr %inst, i32 ptrtoint (ptr getelementptr (%goat.r0, ptr null, i32 1) to i32))
  %v13 = getelementptr inbounds %goat.r0, ptr %v12, i32 0, i32 2
  store i64 %v11, ptr %v13
  %v14 = getelementptr inbounds %goat.r0, ptr %v12, i32 0, i32 2
  %v15 = load i64, ptr %v14
  call void @goat.release(ptr %inst, ptr %v12, i32 0)
  %v16 = call ptr @goat.alloc(ptr %inst, i32 ptrtoint (ptr getelementptr (%goat.v1.t1, ptr null, i32 1) to i32))
  %v17 = getelementptr inbounds i8, ptr %v16, i64 8
  store i32 1, ptr %v17
  %v18 = getelementptr inbounds %goat.v1.t1, ptr %v16, i32 0, i32 4
  store i64 %v15, ptr %v18
  %v19 = getelementptr inbounds i8, ptr %v16, i64 8
  %v20 = load i32, ptr %v19
  switch i32 %v20, label %default22 [ i32 1, label %case23 ]
case23:
  %v24 = getelementptr inbounds %goat.v1.t1, ptr %v16, i32 0, i32 4
  %v25 = load i64, ptr %v24
  br label %join21
default22:
  br label %join21
join21:
  %v26 = phi i64 [ %v25, %case23 ], [ 0, %default22 ]
  call void @goat.release(ptr %inst, ptr %v16, i32 0)
  ret i64 %v26
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
  call void %trap.full(ptr %ctx.full, ptr @goat.text.1, i64 29) noreturn nounwind
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
  call void %trap.stale(ptr %ctx.stale, ptr @goat.text.2, i64 33) noreturn nounwind
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
  call void %trap.over(ptr %ctx.over, ptr @goat.text.1, i64 29) noreturn nounwind
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
  call void %trap.twice(ptr %ctx.twice, ptr @goat.text.3, i64 31) noreturn nounwind
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
  switch i32 %id, label %leaf [ ]
leaf:
  br label %release
release:
  %remaining = phi i32 [ %pending, %leaf ]
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
  call void %trap.twice(ptr %ctx.twice, ptr @goat.text.3, i64 31) noreturn nounwind
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

