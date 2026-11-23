; goat native backend: textual LLVM IR

%goat_host = type { i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
%goat_instance = type { i32, i32, i32, i32, i32, ptr, i64, ptr, ptr, [8 x i64], i64, i64, [55 x ptr] }
%goat_value = type { i32, i64, i64 }

declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)

@goat.text.0 = private unnamed_addr constant [35 x i8] c"this position is outside the string"
@goat.text.1 = private unnamed_addr constant [23 x i8] c"this number got too big"
@goat.text.2 = private unnamed_addr constant [31 x i8] c"a heap block was released twice"


@goat.static.0 = private unnamed_addr constant { i32, i32, i32, [6 x i8] } { i32 -1, i32 0, i32 6, [6 x i8] c"h\C3\A9llo" }
define tailcc i64 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = getelementptr inbounds i8, ptr @goat.static.0, i64 8
  %v2 = load i32, ptr %v1
  %v3 = zext i32 %v2 to i64
  %v4 = sub i64 2, 1
  %v5 = getelementptr inbounds i8, ptr @goat.static.0, i64 8
  %v6 = load i32, ptr %v5
  %v7 = zext i32 %v6 to i64
  %v8 = icmp uge i64 %v4, %v7
  br i1 %v8, label %trap9, label %go10
trap9:
  %v11 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v12 = load ptr, ptr %v11
  %v13 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v14 = load ptr, ptr %v13
  %v15 = getelementptr inbounds %goat_host, ptr %v12, i32 0, i32 9
  %v16 = load ptr, ptr %v15
  call void %v16(ptr %v14, ptr @goat.text.0, i64 35) noreturn nounwind
  unreachable
go10:
  %v17 = add i64 %v4, 12
  %v18 = getelementptr inbounds i8, ptr @goat.static.0, i64 %v17
  %v19 = load i8, ptr %v18
  %v20 = zext i8 %v19 to i64
  %v21 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %v3, i64 %v20)
  %v22 = extractvalue { i64, i1 } %v21, 1
  br i1 %v22, label %trap23, label %go24
trap23:
  %v25 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v26 = load ptr, ptr %v25
  %v27 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v28 = load ptr, ptr %v27
  %v29 = getelementptr inbounds %goat_host, ptr %v26, i32 0, i32 9
  %v30 = load ptr, ptr %v29
  call void %v30(ptr %v28, ptr @goat.text.1, i64 23) noreturn nounwind
  unreachable
go24:
  %v31 = extractvalue { i64, i1 } %v21, 0
  call void @goat.release(ptr %inst, ptr @goat.static.0, i32 0)
  ret i64 %v31
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
  call void %trap.twice(ptr %ctx.twice, ptr @goat.text.2, i64 31) noreturn nounwind
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
  call void %trap.twice(ptr %ctx.twice, ptr @goat.text.2, i64 31) noreturn nounwind
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

