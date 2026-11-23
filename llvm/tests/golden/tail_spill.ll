; goat native backend: textual LLVM IR

%goat_host = type { i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
%goat_instance = type { i32, i32, i32, i32, i32, ptr, i64, ptr, ptr, [8 x i64], i64, i64, [55 x ptr], ptr, ptr, ptr, ptr, ptr, i32, i32, ptr }
%goat_value = type { i32, i64, i64 }

declare ptr @llvm.frameaddress.p0(i32 immarg)
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)
declare { i64, i1 } @llvm.ssub.with.overflow.i64(i64, i64)

@goat.text.0 = private unnamed_addr constant [36 x i8] c"the program called itself too deeply"
@goat.text.1 = private unnamed_addr constant [23 x i8] c"this number got too big"
@goat.text.2 = private unnamed_addr constant [31 x i8] c"a heap block was released twice"


@goat.static.0 = private unnamed_addr constant { i32, i32, i32, i32, i64 } { i32 -1, i32 0, i32 0, i32 0, i64 ptrtoint (ptr @goat_f4 to i64) }
define tailcc i64 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 0
  store i64 0, ptr %v1
  %v2 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 1
  store i64 0, ptr %v2
  %v3 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 2
  store i64 0, ptr %v3
  %v4 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 3
  store i64 0, ptr %v4
  %v5 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 4
  store i64 0, ptr %v5
  %v6 = call ptr @llvm.frameaddress.p0(i32 0)
  %v7 = ptrtoint ptr %v6 to i64
  %v8 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 20
  %v9 = load ptr, ptr %v8
  %v10 = ptrtoint ptr %v9 to i64
  %v11 = icmp ult i64 %v7, %v10
  br i1 %v11, label %trap12, label %go13
trap12:
  %v14 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v15 = load ptr, ptr %v14
  %v16 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v17 = load ptr, ptr %v16
  %v18 = getelementptr inbounds %goat_host, ptr %v15, i32 0, i32 9
  %v19 = load ptr, ptr %v18
  call void %v19(ptr %v17, ptr @goat.text.0, i64 36) noreturn nounwind
  unreachable
go13:
  %v20 = call tailcc i64 @goat_f1(ptr %inst, i64 10, i64 0)
  %v21 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 3
  store i32 238, ptr %v21
  %v22 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 4
  store i32 266, ptr %v22
  %v23 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %v20, i64 0)
  %v24 = extractvalue { i64, i1 } %v23, 1
  br i1 %v24, label %trap25, label %go26
trap25:
  %v27 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v28 = load ptr, ptr %v27
  %v29 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v30 = load ptr, ptr %v29
  %v31 = getelementptr inbounds %goat_host, ptr %v28, i32 0, i32 9
  %v32 = load ptr, ptr %v31
  call void %v32(ptr %v30, ptr @goat.text.1, i64 23) noreturn nounwind
  unreachable
go26:
  %v33 = extractvalue { i64, i1 } %v23, 0
  ret i64 %v33
}

define internal tailcc i64 @goat_f1(ptr %inst, i64 %l0, i64 %l1) nounwind {
entry:
  %v1 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 0
  %v2 = load i64, ptr %v1
  %v3 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 1
  %v4 = load i64, ptr %v3
  %v5 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 2
  %v6 = load i64, ptr %v5
  %v7 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 3
  %v8 = load i64, ptr %v7
  %v9 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 4
  %v10 = load i64, ptr %v9
  %v11 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 0
  store i64 %l1, ptr %v11
  %v12 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 1
  store i64 %v2, ptr %v12
  %v13 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 2
  store i64 %v4, ptr %v13
  %v14 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 3
  store i64 %v6, ptr %v14
  %v15 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 4
  store i64 %v8, ptr %v15
  %v16 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 5
  store i64 %v10, ptr %v16
  %v17 = musttail call tailcc i64 @goat_f2(ptr %inst, ptr @goat.static.0, i64 %l0)
  ret i64 %v17
}

define internal tailcc i64 @goat_f2(ptr %inst, ptr %l0, i64 %l1) nounwind {
entry:
  %v1 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 0
  %v2 = load i64, ptr %v1
  %v3 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 1
  %v4 = load i64, ptr %v3
  %v5 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 2
  %v6 = load i64, ptr %v5
  %v7 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 3
  %v8 = load i64, ptr %v7
  %v9 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 4
  %v10 = load i64, ptr %v9
  %v11 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 5
  %v12 = load i64, ptr %v11
  %v13 = icmp slt i64 %l1, 1
  br i1 %v13, label %then14, label %else15
then14:
  %v17 = getelementptr inbounds i8, ptr %l0, i64 8
  %v18 = load i32, ptr %v17
  call void @goat.release(ptr %inst, ptr %l0, i32 %v18)
  br label %join16
else15:
  %v19 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 3
  store i32 67, ptr %v19
  %v20 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 4
  store i32 72, ptr %v20
  %v21 = call { i64, i1 } @llvm.ssub.with.overflow.i64(i64 %l1, i64 1)
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
  %v32 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 3
  store i32 74, ptr %v32
  %v33 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 4
  store i32 79, ptr %v33
  %v34 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %v2, i64 1)
  %v35 = extractvalue { i64, i1 } %v34, 1
  br i1 %v35, label %trap36, label %go37
trap36:
  %v38 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v39 = load ptr, ptr %v38
  %v40 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v41 = load ptr, ptr %v40
  %v42 = getelementptr inbounds %goat_host, ptr %v39, i32 0, i32 9
  %v43 = load ptr, ptr %v42
  call void %v43(ptr %v41, ptr @goat.text.1, i64 23) noreturn nounwind
  unreachable
go37:
  %v44 = extractvalue { i64, i1 } %v34, 0
  %v45 = getelementptr inbounds i8, ptr %l0, i64 16
  %v46 = load i64, ptr %v45
  %v47 = inttoptr i64 %v46 to ptr
  %v48 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 0
  store i64 %v44, ptr %v48
  %v49 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 1
  store i64 %v4, ptr %v49
  %v50 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 2
  store i64 %v6, ptr %v50
  %v51 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 3
  store i64 %v8, ptr %v51
  %v52 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 4
  store i64 %v10, ptr %v52
  %v53 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 5
  store i64 %v12, ptr %v53
  %v54 = musttail call tailcc i64 %v47(ptr %inst, ptr %l0, i64 %v31)
  ret i64 %v54
join16:
  %v55 = phi i64 [ %v2, %then14 ]
  ret i64 %v55
}

define internal tailcc i64 @goat_f3(ptr %inst, i64 %l0, i64 %l1) nounwind {
entry:
  %v1 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 0
  %v2 = load i64, ptr %v1
  %v3 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 1
  %v4 = load i64, ptr %v3
  %v5 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 2
  %v6 = load i64, ptr %v5
  %v7 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 3
  %v8 = load i64, ptr %v7
  %v9 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 4
  %v10 = load i64, ptr %v9
  %v11 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 0
  store i64 %v2, ptr %v11
  %v12 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 1
  store i64 %v4, ptr %v12
  %v13 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 2
  store i64 %v6, ptr %v13
  %v14 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 3
  store i64 %v8, ptr %v14
  %v15 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 4
  store i64 %v10, ptr %v15
  %v16 = musttail call tailcc i64 @goat_f1(ptr %inst, i64 %l0, i64 %l1)
  ret i64 %v16
}

define internal tailcc i64 @goat_f4(ptr %inst, ptr %env, i64 %l0) nounwind {
entry:
  %v1 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 0
  %v2 = load i64, ptr %v1
  %v3 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 1
  %v4 = load i64, ptr %v3
  %v5 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 2
  %v6 = load i64, ptr %v5
  %v7 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 3
  %v8 = load i64, ptr %v7
  %v9 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 4
  %v10 = load i64, ptr %v9
  %v11 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 5
  %v12 = load i64, ptr %v11
  %v13 = getelementptr inbounds i8, ptr %env, i64 8
  %v14 = load i32, ptr %v13
  call void @goat.release(ptr %inst, ptr %env, i32 %v14)
  %v15 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 0
  store i64 %v4, ptr %v15
  %v16 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 1
  store i64 %v6, ptr %v16
  %v17 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 2
  store i64 %v8, ptr %v17
  %v18 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 3
  store i64 %v10, ptr %v18
  %v19 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 9, i32 4
  store i64 %v12, ptr %v19
  %v20 = musttail call tailcc i64 @goat_f3(ptr %inst, i64 %l0, i64 %v2)
  ret i64 %v20
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
  %instance_old = icmp ult i32 %instance_version, 3
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

