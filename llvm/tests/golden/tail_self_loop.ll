; goat native backend: textual LLVM IR

%goat_host = type { i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
%goat_instance = type { i32, i32, i32, i32, i32, ptr, i64, ptr, ptr, [8 x i64], i64, i64, [55 x ptr] }
%goat_value = type { i32, i64, i64 }

declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)
declare { i64, i1 } @llvm.ssub.with.overflow.i64(i64, i64)

@goat.text.0 = private unnamed_addr constant [23 x i8] c"this number got too big"


define tailcc i64 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = call tailcc i64 @goat_f1(ptr %inst, i64 10, i64 0)
  %v2 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 3
  store i32 83, ptr %v2
  %v3 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 4
  store i32 99, ptr %v3
  %v4 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %v1, i64 0)
  %v5 = extractvalue { i64, i1 } %v4, 1
  br i1 %v5, label %trap6, label %go7
trap6:
  %v8 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v9 = load ptr, ptr %v8
  %v10 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v11 = load ptr, ptr %v10
  %v12 = getelementptr inbounds %goat_host, ptr %v9, i32 0, i32 9
  %v13 = load ptr, ptr %v12
  call void %v13(ptr %v11, ptr @goat.text.0, i64 23) noreturn nounwind
  unreachable
go7:
  %v14 = extractvalue { i64, i1 } %v4, 0
  ret i64 %v14
}

define internal tailcc i64 @goat_f1(ptr %inst, i64 %in0, i64 %in1) nounwind {
entry:
  br label %loop
loop:
  %s0 = phi i64 [ %in0, %entry ], [ %v17, %go23 ]
  %s1 = phi i64 [ %in1, %entry ], [ %v30, %go23 ]
  %v1 = icmp eq i64 %s0, 0
  br i1 %v1, label %then2, label %else3
then2:
  br label %join4
else3:
  %v5 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 3
  store i32 57, ptr %v5
  %v6 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 4
  store i32 62, ptr %v6
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
  call void %v16(ptr %v14, ptr @goat.text.0, i64 23) noreturn nounwind
  unreachable
go10:
  %v17 = extractvalue { i64, i1 } %v7, 0
  %v18 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 3
  store i32 64, ptr %v18
  %v19 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 4
  store i32 71, ptr %v19
  %v20 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %s1, i64 1)
  %v21 = extractvalue { i64, i1 } %v20, 1
  br i1 %v21, label %trap22, label %go23
trap22:
  %v24 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v25 = load ptr, ptr %v24
  %v26 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v27 = load ptr, ptr %v26
  %v28 = getelementptr inbounds %goat_host, ptr %v25, i32 0, i32 9
  %v29 = load ptr, ptr %v28
  call void %v29(ptr %v27, ptr @goat.text.0, i64 23) noreturn nounwind
  unreachable
go23:
  %v30 = extractvalue { i64, i1 } %v20, 0
  br label %loop
join4:
  %v31 = phi i64 [ %s1, %then2 ]
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
