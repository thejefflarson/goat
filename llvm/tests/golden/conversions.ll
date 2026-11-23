; goat native backend: textual LLVM IR

%goat_host = type { i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
%goat_instance = type { i32, i32, i32, i32, i32, ptr, i64, ptr, ptr, [8 x i64], i64, i64, [55 x ptr] }
%goat_value = type { i32, i64, i64 }

declare double @llvm.sqrt.f64(double)
declare double @llvm.trunc.f64(double)

@goat.text.0 = private unnamed_addr constant [40 x i8] c"this number can't be made a whole number"


define tailcc i64 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = sitofp i64 17 to double
  %v2 = call double @llvm.sqrt.f64(double %v1)
  %v3 = call double @llvm.trunc.f64(double %v2)
  %v4 = fcmp oge double %v3, 0xC3E0000000000000
  %v5 = fcmp olt double %v3, 0x43E0000000000000
  %v6 = and i1 %v4, %v5
  %v7 = xor i1 %v6, true
  br i1 %v7, label %trap8, label %go9
trap8:
  %v10 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v11 = load ptr, ptr %v10
  %v12 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v13 = load ptr, ptr %v12
  %v14 = getelementptr inbounds %goat_host, ptr %v11, i32 0, i32 9
  %v15 = load ptr, ptr %v14
  call void %v15(ptr %v13, ptr @goat.text.0, i64 40) noreturn nounwind
  unreachable
go9:
  %v16 = fptosi double %v3 to i64
  ret i64 %v16
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
