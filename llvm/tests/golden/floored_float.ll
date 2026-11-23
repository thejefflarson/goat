; goat native backend: textual LLVM IR

%goat_host = type { i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
%goat_instance = type { i32, i32, i32, i32, i32, ptr, i64, ptr, ptr, [8 x i64], i64, i64, [55 x ptr] }
%goat_value = type { i32, i64, i64 }

declare double @llvm.copysign.f64(double, double)
declare double @llvm.floor.f64(double)



define internal double @goat.float_floor_div(double %x, double %y) nounwind {
entry:
  %yz = fcmp oeq double %y, 0.0
  br i1 %yz, label %zero, label %go
zero:
  %zq = fdiv double %x, %y
  ret double %zq
go:
  %m0 = frem double %x, %y
  %xm = fsub double %x, %m0
  %d = fdiv double %xm, %y
  %mnz = fcmp une double %m0, 0.0
  br i1 %mnz, label %nz, label %z
nz:
  %yneg = fcmp olt double %y, 0.0
  %mneg = fcmp olt double %m0, 0.0
  %diff = xor i1 %yneg, %mneg
  %ma = fadd double %m0, %y
  %da = fsub double %d, 1.0
  %m1 = select i1 %diff, double %ma, double %m0
  %d1 = select i1 %diff, double %da, double %d
  br label %join
z:
  %m2 = call double @llvm.copysign.f64(double 0.0, double %y)
  br label %join
join:
  %m = phi double [ %m1, %nz ], [ %m2, %z ]
  %dd = phi double [ %d1, %nz ], [ %d, %z ]
  %dnz = fcmp une double %dd, 0.0
  br i1 %dnz, label %fl, label %fz
fl:
  %f0 = call double @llvm.floor.f64(double %dd)
  %fr = fsub double %dd, %f0
  %gt = fcmp ogt double %fr, 0.5
  %fp = fadd double %f0, 1.0
  %f1 = select i1 %gt, double %fp, double %f0
  br label %end
fz:
  %xy = fdiv double %x, %y
  %f2 = call double @llvm.copysign.f64(double 0.0, double %xy)
  br label %end
end:
  %q = phi double [ %f1, %fl ], [ %f2, %fz ]
  ret double %q
}

define internal double @goat.float_floor_mod(double %x, double %y) nounwind {
entry:
  %m0 = frem double %x, %y
  %xm = fsub double %x, %m0
  %d = fdiv double %xm, %y
  %mnz = fcmp une double %m0, 0.0
  br i1 %mnz, label %nz, label %z
nz:
  %yneg = fcmp olt double %y, 0.0
  %mneg = fcmp olt double %m0, 0.0
  %diff = xor i1 %yneg, %mneg
  %ma = fadd double %m0, %y
  %da = fsub double %d, 1.0
  %m1 = select i1 %diff, double %ma, double %m0
  %d1 = select i1 %diff, double %da, double %d
  br label %join
z:
  %m2 = call double @llvm.copysign.f64(double 0.0, double %y)
  br label %join
join:
  %m = phi double [ %m1, %nz ], [ %m2, %z ]
  %dd = phi double [ %d1, %nz ], [ %d, %z ]
  %dnz = fcmp une double %dd, 0.0
  br i1 %dnz, label %fl, label %fz
fl:
  %f0 = call double @llvm.floor.f64(double %dd)
  %fr = fsub double %dd, %f0
  %gt = fcmp ogt double %fr, 0.5
  %fp = fadd double %f0, 1.0
  %f1 = select i1 %gt, double %fp, double %f0
  br label %end
fz:
  %xy = fdiv double %x, %y
  %f2 = call double @llvm.copysign.f64(double 0.0, double %xy)
  br label %end
end:
  %q = phi double [ %f1, %fl ], [ %f2, %fz ]
  ret double %m
}

define tailcc double @goat_entry(ptr %inst) nounwind {
entry:
  %v1 = call double @goat.float_floor_div(double 0x401E000000000000, double 0xC000000000000000)
  %v2 = call double @goat.float_floor_mod(double 0x401E000000000000, double 0xC000000000000000)
  %v3 = fadd double %v1, %v2
  ret double %v3
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
  %v = call tailcc double @goat_entry(ptr %inst)
  %print_slot = getelementptr inbounds %goat_host, ptr %host, i32 0, i32 1
  %print = load ptr, ptr %print_slot
  call void %print(ptr %ctx, double %v) nounwind
  ret i32 0
}
