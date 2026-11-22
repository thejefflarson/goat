;; The arithmetic of one particle step, `p = p + v; v = v * damping`, over a flat
;; array of {px, py, vx, vy} f64 quadruples with no allocation: the most a
;; SIMD path could save if the records were unboxed and the loop were all there
;; was. `scalar` does four f64 operations per particle, `simd` two f64x2.
;;
;; Assemble for V8 with
;;   wasm-as --enable-simd inner_loop.wat -o inner_loop.wasm
;; The wasmtime harness reads this text directly.
(module
  (memory (export "memory") 1)

  (func (export "init") (param $n i32)
    (local $i i32)
    (loop $next
      (f64.store (i32.shl (local.get $i) (i32.const 3))
        (f64.add (f64.convert_i32_u (local.get $i)) (f64.const 0.5)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br_if $next (i32.lt_u (local.get $i) (i32.shl (local.get $n) (i32.const 2))))))

  (func (export "scalar") (param $n i32) (param $reps i32) (result f64)
    (local $i i32) (local $at i32)
    (loop $rep
      (local.set $i (i32.const 0))
      (loop $each
        (local.set $at (i32.shl (local.get $i) (i32.const 5)))
        (f64.store (local.get $at)
          (f64.add (f64.load (local.get $at)) (f64.load offset=16 (local.get $at))))
        (f64.store offset=8 (local.get $at)
          (f64.add (f64.load offset=8 (local.get $at)) (f64.load offset=24 (local.get $at))))
        (f64.store offset=16 (local.get $at)
          (f64.mul (f64.load offset=16 (local.get $at)) (f64.const 0.999)))
        (f64.store offset=24 (local.get $at)
          (f64.mul (f64.load offset=24 (local.get $at)) (f64.const 0.999)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br_if $each (i32.lt_u (local.get $i) (local.get $n))))
      (local.set $reps (i32.sub (local.get $reps) (i32.const 1)))
      (br_if $rep (local.get $reps)))
    (f64.load (i32.const 0)))

  (func (export "simd") (param $n i32) (param $reps i32) (result f64)
    (local $i i32) (local $at i32) (local $damp v128)
    (local.set $damp (v128.const f64x2 0.999 0.999))
    (loop $rep
      (local.set $i (i32.const 0))
      (loop $each
        (local.set $at (i32.shl (local.get $i) (i32.const 5)))
        (v128.store (local.get $at)
          (f64x2.add (v128.load (local.get $at)) (v128.load offset=16 (local.get $at))))
        (v128.store offset=16 (local.get $at)
          (f64x2.mul (v128.load offset=16 (local.get $at)) (local.get $damp)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br_if $each (i32.lt_u (local.get $i) (local.get $n))))
      (local.set $reps (i32.sub (local.get $reps) (i32.const 1)))
      (br_if $rep (local.get $reps)))
    (f64.load (i32.const 0))))
