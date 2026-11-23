; goat native backend: textual LLVM IR

%goat_host = type { i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
%goat_instance = type { i32, i32, i32, i32, i32, ptr, i64, ptr, ptr, [8 x i64], i64, i64, [55 x ptr] }
%goat_value = type { i32, i64, i64 }

declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)

@goat.text.0 = private unnamed_addr constant [23 x i8] c"this number got too big"


define i64 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = call i64 @goat_f1(ptr %inst, i64 20, i64 22)
  ret i64 %v1
}

define internal i64 @goat_f1(ptr %inst, i64 %l0, i64 %l1) nounwind {
entry:
  %v1 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %l0, i64 %l1)
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
  ret i64 %v11
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
  %v = call i64 @goat_entry(ptr %inst)
  %print_slot = getelementptr inbounds %goat_host, ptr %host, i32 0, i32 3
  %print = load ptr, ptr %print_slot
  call void %print(ptr %ctx, i64 %v) nounwind
  ret i32 0
}
