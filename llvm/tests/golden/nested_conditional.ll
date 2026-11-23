; goat native backend: textual LLVM IR

declare void @goat_trap(ptr, ptr, i32) noreturn nounwind
declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)

@goat.trap.0 = private unnamed_addr constant [23 x i8] c"this number got too big"
@goat.trap.1 = private unnamed_addr constant [5 x i8] c"never"

define i64 @goat_entry(ptr %inst) nounwind {
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
  call void @goat_trap(ptr %inst, ptr @goat.trap.0, i32 23)
  unreachable
go11:
  %v12 = extractvalue { i64, i1 } %v8, 0
  br label %join7
join7:
  %v13 = phi i64 [ 1, %then5 ], [ %v12, %go11 ]
  br label %join4
else3:
  call void @goat_trap(ptr %inst, ptr @goat.trap.1, i32 5)
  unreachable
join4:
  %v14 = phi i64 [ %v13, %join7 ]
  ret i64 %v14
}

