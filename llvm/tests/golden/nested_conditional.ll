; goat native backend: textual LLVM IR

%goat_host = type { i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
%goat_instance = type { i32, i32, i32, i32, i32, ptr, i64, ptr, ptr, [8 x i64], i64, i64, [55 x ptr] }
%goat_value = type { i32, i64, i64 }

declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)

@goat.text.0 = private unnamed_addr constant [23 x i8] c"this number got too big"
@goat.text.1 = private unnamed_addr constant [5 x i8] c"never"


define tailcc i64 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = icmp sgt i64 2, 1
  br i1 %v1, label %then2, label %else3
then2:
  br i1 false, label %then5, label %else6
then5:
  br label %join7
else6:
  %v8 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 2, i64 3)
  %v9 = extractvalue { i64, i1 } %v8, 1
  br i1 %v9, label %trap10, label %go11
trap10:
  %v12 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v13 = load ptr, ptr %v12
  %v14 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v15 = load ptr, ptr %v14
  %v16 = getelementptr inbounds %goat_host, ptr %v13, i32 0, i32 9
  %v17 = load ptr, ptr %v16
  call void %v17(ptr %v15, ptr @goat.text.0, i64 23) noreturn nounwind
  unreachable
go11:
  %v18 = extractvalue { i64, i1 } %v8, 0
  br label %join7
join7:
  %v19 = phi i64 [ 1, %then5 ], [ %v18, %go11 ]
  br label %join4
else3:
  %v20 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v21 = load ptr, ptr %v20
  %v22 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v23 = load ptr, ptr %v22
  %v24 = getelementptr inbounds %goat_host, ptr %v21, i32 0, i32 9
  %v25 = load ptr, ptr %v24
  call void %v25(ptr %v23, ptr @goat.text.1, i64 5) noreturn nounwind
  unreachable
join4:
  %v26 = phi i64 [ %v19, %join7 ]
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
