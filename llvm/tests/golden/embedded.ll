; goat native backend: textual LLVM IR

%goat_host = type { i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
%goat_instance = type { i32, i32, i32, i32, i32, ptr, i64, ptr, ptr, [8 x i64] }

declare { i32, i1 } @llvm.sadd.with.overflow.i32(i32, i32)
declare { i32, i1 } @llvm.smul.with.overflow.i32(i32, i32)
declare { i32, i1 } @llvm.ssub.with.overflow.i32(i32, i32)

@goat.trap.0 = private unnamed_addr constant [23 x i8] c"this number got too big"

define i32 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 2, i32 3)
  %v2 = extractvalue { i32, i1 } %v1, 1
  br i1 %v2, label %trap3, label %go4
trap3:
  %v5 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v6 = load ptr, ptr %v5
  %v7 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v8 = load ptr, ptr %v7
  %v9 = getelementptr inbounds %goat_host, ptr %v6, i32 0, i32 9
  %v10 = load ptr, ptr %v9
  call void %v10(ptr %v8, ptr @goat.trap.0, i64 23) noreturn nounwind
  unreachable
go4:
  %v11 = extractvalue { i32, i1 } %v1, 0
  %v12 = call { i32, i1 } @llvm.ssub.with.overflow.i32(i32 10, i32 4)
  %v13 = extractvalue { i32, i1 } %v12, 1
  br i1 %v13, label %trap14, label %go15
trap14:
  %v16 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v17 = load ptr, ptr %v16
  %v18 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v19 = load ptr, ptr %v18
  %v20 = getelementptr inbounds %goat_host, ptr %v17, i32 0, i32 9
  %v21 = load ptr, ptr %v20
  call void %v21(ptr %v19, ptr @goat.trap.0, i64 23) noreturn nounwind
  unreachable
go15:
  %v22 = extractvalue { i32, i1 } %v12, 0
  %v23 = call { i32, i1 } @llvm.smul.with.overflow.i32(i32 %v11, i32 %v22)
  %v24 = extractvalue { i32, i1 } %v23, 1
  br i1 %v24, label %trap25, label %go26
trap25:
  %v27 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v28 = load ptr, ptr %v27
  %v29 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v30 = load ptr, ptr %v29
  %v31 = getelementptr inbounds %goat_host, ptr %v28, i32 0, i32 9
  %v32 = load ptr, ptr %v31
  call void %v32(ptr %v30, ptr @goat.trap.0, i64 23) noreturn nounwind
  unreachable
go26:
  %v33 = extractvalue { i32, i1 } %v23, 0
  ret i32 %v33
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
  %instance_old = icmp ult i32 %instance_version, 1
  br i1 %instance_old, label %bad_instance, label %run
bad_instance:
  ret i32 2
run:
  %host_slot = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  store ptr %host, ptr %host_slot
  %ctx_slot = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  store ptr %ctx, ptr %ctx_slot
  %v = call i32 @goat_entry(ptr %inst)
  %w = sext i32 %v to i64
  %print_slot = getelementptr inbounds %goat_host, ptr %host, i32 0, i32 3
  %print = load ptr, ptr %print_slot
  call void %print(ptr %ctx, i64 %w) nounwind
  ret i32 0
}
