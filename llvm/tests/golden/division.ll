; goat native backend: textual LLVM IR

%goat_host = type { i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
%goat_instance = type { i32, i32, i32, i32, i32, ptr, i64, ptr, ptr, [8 x i64] }

declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)

@goat.trap.0 = private unnamed_addr constant [16 x i8] c"division by zero"
@goat.trap.1 = private unnamed_addr constant [23 x i8] c"this number got too big"

define i64 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = icmp eq i64 -2, 0
  br i1 %v1, label %trap2, label %go3
trap2:
  %v4 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v5 = load ptr, ptr %v4
  %v6 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v7 = load ptr, ptr %v6
  %v8 = getelementptr inbounds %goat_host, ptr %v5, i32 0, i32 9
  %v9 = load ptr, ptr %v8
  call void %v9(ptr %v7, ptr @goat.trap.0, i64 16) noreturn nounwind
  unreachable
go3:
  %v10 = icmp eq i64 7, -9223372036854775808
  %v11 = icmp eq i64 -2, -1
  %v12 = and i1 %v10, %v11
  br i1 %v12, label %trap13, label %go14
trap13:
  %v15 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v16 = load ptr, ptr %v15
  %v17 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v18 = load ptr, ptr %v17
  %v19 = getelementptr inbounds %goat_host, ptr %v16, i32 0, i32 9
  %v20 = load ptr, ptr %v19
  call void %v20(ptr %v18, ptr @goat.trap.1, i64 23) noreturn nounwind
  unreachable
go14:
  %v21 = sdiv i64 7, -2
  %v22 = icmp eq i64 -2, 0
  br i1 %v22, label %trap23, label %go24
trap23:
  %v25 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v26 = load ptr, ptr %v25
  %v27 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v28 = load ptr, ptr %v27
  %v29 = getelementptr inbounds %goat_host, ptr %v26, i32 0, i32 9
  %v30 = load ptr, ptr %v29
  call void %v30(ptr %v28, ptr @goat.trap.0, i64 16) noreturn nounwind
  unreachable
go24:
  %v31 = icmp eq i64 7, -9223372036854775808
  %v32 = icmp eq i64 -2, -1
  %v33 = and i1 %v31, %v32
  br i1 %v33, label %trap34, label %go35
trap34:
  %v36 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v37 = load ptr, ptr %v36
  %v38 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v39 = load ptr, ptr %v38
  %v40 = getelementptr inbounds %goat_host, ptr %v37, i32 0, i32 9
  %v41 = load ptr, ptr %v40
  call void %v41(ptr %v39, ptr @goat.trap.1, i64 23) noreturn nounwind
  unreachable
go35:
  %v42 = srem i64 7, -2
  %v43 = icmp ne i64 %v42, 0
  %v44 = xor i64 %v42, -2
  %v45 = icmp slt i64 %v44, 0
  %v46 = and i1 %v43, %v45
  %v47 = sdiv i64 7, -2
  %v48 = sub i64 %v47, 1
  %v49 = select i1 %v46, i64 %v48, i64 %v47
  %v50 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %v21, i64 %v49)
  %v51 = extractvalue { i64, i1 } %v50, 1
  br i1 %v51, label %trap52, label %go53
trap52:
  %v54 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v55 = load ptr, ptr %v54
  %v56 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v57 = load ptr, ptr %v56
  %v58 = getelementptr inbounds %goat_host, ptr %v55, i32 0, i32 9
  %v59 = load ptr, ptr %v58
  call void %v59(ptr %v57, ptr @goat.trap.1, i64 23) noreturn nounwind
  unreachable
go53:
  %v60 = extractvalue { i64, i1 } %v50, 0
  %v61 = icmp eq i64 -2, 0
  br i1 %v61, label %trap62, label %go63
trap62:
  %v64 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v65 = load ptr, ptr %v64
  %v66 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v67 = load ptr, ptr %v66
  %v68 = getelementptr inbounds %goat_host, ptr %v65, i32 0, i32 9
  %v69 = load ptr, ptr %v68
  call void %v69(ptr %v67, ptr @goat.trap.0, i64 16) noreturn nounwind
  unreachable
go63:
  %v70 = icmp eq i64 -2, -1
  %v71 = select i1 %v70, i64 1, i64 -2
  %v72 = srem i64 7, %v71
  %v73 = icmp ne i64 %v72, 0
  %v74 = xor i64 %v72, -2
  %v75 = icmp slt i64 %v74, 0
  %v76 = and i1 %v73, %v75
  %v77 = add i64 %v72, -2
  %v78 = select i1 %v76, i64 %v77, i64 %v72
  %v79 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %v60, i64 %v78)
  %v80 = extractvalue { i64, i1 } %v79, 1
  br i1 %v80, label %trap81, label %go82
trap81:
  %v83 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 7
  %v84 = load ptr, ptr %v83
  %v85 = getelementptr inbounds %goat_instance, ptr %inst, i32 0, i32 8
  %v86 = load ptr, ptr %v85
  %v87 = getelementptr inbounds %goat_host, ptr %v84, i32 0, i32 9
  %v88 = load ptr, ptr %v87
  call void %v88(ptr %v86, ptr @goat.trap.1, i64 23) noreturn nounwind
  unreachable
go82:
  %v89 = extractvalue { i64, i1 } %v79, 0
  ret i64 %v89
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
  %v = call i64 @goat_entry(ptr %inst)
  %print_slot = getelementptr inbounds %goat_host, ptr %host, i32 0, i32 3
  %print = load ptr, ptr %print_slot
  call void %print(ptr %ctx, i64 %v) nounwind
  ret i32 0
}
