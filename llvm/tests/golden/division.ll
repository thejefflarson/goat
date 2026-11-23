; goat native backend: textual LLVM IR

declare void @goat_trap(ptr, ptr, i32) noreturn nounwind
declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)

@goat.trap.0 = private unnamed_addr constant [16 x i8] c"division by zero"
@goat.trap.1 = private unnamed_addr constant [23 x i8] c"this number got too big"

define i64 @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = icmp eq i64 -2, 0
  br i1 %v1, label %trap2, label %go3
trap2:
  call void @goat_trap(ptr %inst, ptr @goat.trap.0, i32 16)
  unreachable
go3:
  %v4 = icmp eq i64 7, -9223372036854775808
  %v5 = icmp eq i64 -2, -1
  %v6 = and i1 %v4, %v5
  br i1 %v6, label %trap7, label %go8
trap7:
  call void @goat_trap(ptr %inst, ptr @goat.trap.1, i32 23)
  unreachable
go8:
  %v9 = sdiv i64 7, -2
  %v10 = icmp eq i64 -2, 0
  br i1 %v10, label %trap11, label %go12
trap11:
  call void @goat_trap(ptr %inst, ptr @goat.trap.0, i32 16)
  unreachable
go12:
  %v13 = icmp eq i64 7, -9223372036854775808
  %v14 = icmp eq i64 -2, -1
  %v15 = and i1 %v13, %v14
  br i1 %v15, label %trap16, label %go17
trap16:
  call void @goat_trap(ptr %inst, ptr @goat.trap.1, i32 23)
  unreachable
go17:
  %v18 = srem i64 7, -2
  %v19 = icmp ne i64 %v18, 0
  %v20 = xor i64 %v18, -2
  %v21 = icmp slt i64 %v20, 0
  %v22 = and i1 %v19, %v21
  %v23 = sdiv i64 7, -2
  %v24 = sub i64 %v23, 1
  %v25 = select i1 %v22, i64 %v24, i64 %v23
  %v26 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %v9, i64 %v25)
  %v27 = extractvalue { i64, i1 } %v26, 1
  br i1 %v27, label %trap28, label %go29
trap28:
  call void @goat_trap(ptr %inst, ptr @goat.trap.1, i32 23)
  unreachable
go29:
  %v30 = extractvalue { i64, i1 } %v26, 0
  %v31 = icmp eq i64 -2, 0
  br i1 %v31, label %trap32, label %go33
trap32:
  call void @goat_trap(ptr %inst, ptr @goat.trap.0, i32 16)
  unreachable
go33:
  %v34 = icmp eq i64 -2, -1
  %v35 = select i1 %v34, i64 1, i64 -2
  %v36 = srem i64 7, %v35
  %v37 = icmp ne i64 %v36, 0
  %v38 = xor i64 %v36, -2
  %v39 = icmp slt i64 %v38, 0
  %v40 = and i1 %v37, %v39
  %v41 = add i64 %v36, -2
  %v42 = select i1 %v40, i64 %v41, i64 %v36
  %v43 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %v30, i64 %v42)
  %v44 = extractvalue { i64, i1 } %v43, 1
  br i1 %v44, label %trap45, label %go46
trap45:
  call void @goat_trap(ptr %inst, ptr @goat.trap.1, i32 23)
  unreachable
go46:
  %v47 = extractvalue { i64, i1 } %v43, 0
  ret i64 %v47
}

