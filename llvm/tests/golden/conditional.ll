; goat native backend: textual LLVM IR

%goat_host = type { i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
%goat_instance = type { i32, i32, i32, i32, i32, ptr, i64, ptr, ptr, [8 x i64], i64, i64, [55 x ptr] }
%goat_value = type { i32, i64, i64 }




define double @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = fcmp olt double 0x4008000000000000, 0x4014000000000000
  br i1 %v1, label %then2, label %else3
then2:
  %v5 = fadd double 0x4008000000000000, 0x3FF0000000000000
  br label %join4
else3:
  br label %join4
join4:
  %v6 = phi double [ %v5, %then2 ], [ 0x4008000000000000, %else3 ]
  ret double %v6
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
  %v = call double @goat_entry(ptr %inst)
  %print_slot = getelementptr inbounds %goat_host, ptr %host, i32 0, i32 1
  %print = load ptr, ptr %print_slot
  call void %print(ptr %ctx, double %v) nounwind
  ret i32 0
}
