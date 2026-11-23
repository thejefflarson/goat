; goat native backend: textual LLVM IR

%goat_host = type { i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
%goat_instance = type { i32, i32, i32, i32, i32, ptr, i64, ptr, ptr, [8 x i64], i64, i64, [55 x ptr], ptr, ptr, ptr, ptr, ptr, i32, i32, ptr }
%goat_value = type { i32, i64, i64 }

declare ptr @llvm.frameaddress.p0(i32 immarg)
declare { i64, i1 } @llvm.ssub.with.overflow.i64(i64, i64)

@goat.text.0 = private unnamed_addr constant [36 x i8] c"the program called itself too deeply"
@goat.text.1 = private unnamed_addr constant [23 x i8] c"this number got too big"


define tailcc i64 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = call ptr @llvm.frameaddress.p0(i32 0)
  %v2 = ptrtoint ptr %v1 to i64
  %v3 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 20
  %v4 = load ptr, ptr %v3
  %v5 = ptrtoint ptr %v4 to i64
  %v6 = icmp ult i64 %v2, %v5
  br i1 %v6, label %trap7, label %go8
trap7:
  %v9 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v10 = load ptr, ptr %v9
  %v11 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v12 = load ptr, ptr %v11
  %v13 = getelementptr inbounds %goat_host, ptr %v10, i32 0, i32 9
  %v14 = load ptr, ptr %v13
  call void %v14(ptr %v12, ptr @goat.text.0, i64 36) noreturn nounwind
  unreachable
go8:
  %v15 = call tailcc i1 @goat_g0(ptr %inst, i32 0, i64 10, i64 undef)
  br i1 %v15, label %then16, label %else17
then16:
  br label %join18
else17:
  br label %join18
join18:
  %v19 = phi i64 [ 1, %then16 ], [ 0, %else17 ]
  ret i64 %v19
}

define internal tailcc i1 @goat_g0(ptr %inst, i32 %in_which, i64 %in0, i64 %in1) nounwind {
entry:
  br label %loop
loop:
  %which = phi i32 [ %in_which, %entry ], [ 1, %go10 ], [ 0, %go28 ]
  %s0 = phi i64 [ %in0, %entry ], [ %v17, %go10 ], [ %v35, %go28 ]
  %s1 = phi i64 [ %in1, %entry ], [ 0, %go10 ], [ undef, %go28 ]
  switch i32 %which, label %member.1 [ i32 0, label %member.0 ]
member.0:
  %v1 = icmp slt i64 %s0, 1
  br i1 %v1, label %then2, label %else3
then2:
  br label %join4
else3:
  %v5 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 3
  store i32 55, ptr %v5
  %v6 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 4
  store i32 60, ptr %v6
  %v7 = call { i64, i1 } @llvm.ssub.with.overflow.i64(i64 %s0, i64 1)
  %v8 = extractvalue { i64, i1 } %v7, 1
  br i1 %v8, label %trap9, label %go10
trap9:
  %v11 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v12 = load ptr, ptr %v11
  %v13 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v14 = load ptr, ptr %v13
  %v15 = getelementptr inbounds %goat_host, ptr %v12, i32 0, i32 9
  %v16 = load ptr, ptr %v15
  call void %v16(ptr %v14, ptr @goat.text.1, i64 23) noreturn nounwind
  unreachable
go10:
  %v17 = extractvalue { i64, i1 } %v7, 0
  br label %loop
join4:
  %v18 = phi i1 [ true, %then2 ]
  ret i1 %v18
member.1:
  %v19 = icmp slt i64 %s0, 1
  br i1 %v19, label %then20, label %else21
then20:
  br label %join22
else21:
  %v23 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 3
  store i32 137, ptr %v23
  %v24 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 4
  store i32 142, ptr %v24
  %v25 = call { i64, i1 } @llvm.ssub.with.overflow.i64(i64 %s0, i64 1)
  %v26 = extractvalue { i64, i1 } %v25, 1
  br i1 %v26, label %trap27, label %go28
trap27:
  %v29 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v30 = load ptr, ptr %v29
  %v31 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v32 = load ptr, ptr %v31
  %v33 = getelementptr inbounds %goat_host, ptr %v30, i32 0, i32 9
  %v34 = load ptr, ptr %v33
  call void %v34(ptr %v32, ptr @goat.text.1, i64 23) noreturn nounwind
  unreachable
go28:
  %v35 = extractvalue { i64, i1 } %v25, 0
  br label %loop
join22:
  %v36 = phi i1 [ false, %then20 ]
  ret i1 %v36
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
