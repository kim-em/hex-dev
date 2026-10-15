
/home/kim/.codex/tasks/hex-10575/orderedfn-scan-investigation/hexorderedfn_bench-scan:     file format elf64-x86-64


Disassembly of section .text:

0000000000b87120 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5>:
  b87120:	push   %rbp
  b87121:	push   %r15
  b87123:	push   %r14
  b87125:	push   %r13
  b87127:	push   %r12
  b87129:	push   %rbx
  b8712a:	push   %rax
  b8712b:	mov    %rdi,%rbx
  b8712e:	xchg   %ax,%ax
  b87130:	mov    %rsi,%rbp
  b87133:	mov    0x8(%rbx),%rax
  b87137:	lea    0x1(,%rax,2),%rsi
  b8713f:	test   $0x1,%bpl
  b87143:	je     b871da <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0xba>
  b87149:	cmp    %rsi,%rbp
  b8714c:	jae    b872e2 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x1c2>
  b87152:	mov    0x40f4400(%rip),%eax        # 4c7b558 <lp_Hex_Hex_DensePoly_trimTrailingZerosGo___at___00Hex_DensePoly_trimTrailingZerosImpl___at___00Hex_DensePoly_ofCoeffs___at___00Hex_DensePoly_zero___at___00Hex_DensePoly_monomial___at___00Hex_OrderedFnBench_prepSecond_spec__1_spec__1_spec__2_spec__5_spec__6___closed__1_once>
  b87158:	cmp    $0x1,%eax
  b8715b:	jne    b871ef <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0xcf>
  b87161:	mov    0x40f43e8(%rip),%r15        # 4c7b550 <lp_Hex_Hex_DensePoly_trimTrailingZerosGo___at___00Hex_DensePoly_trimTrailingZerosImpl___at___00Hex_DensePoly_ofCoeffs___at___00Hex_DensePoly_zero___at___00Hex_DensePoly_monomial___at___00Hex_OrderedFnBench_prepSecond_spec__1_spec__1_spec__2_spec__5_spec__6___closed__1>
  b87168:	mov    0x40f448a(%rip),%eax        # 4c7b5f8 <lp_Hex_Hex_DensePoly_trimTrailingZerosGo___at___00Hex_DensePoly_trimTrailingZerosImpl___at___00Hex_DensePoly_ofCoeffs___at___00Hex_DensePoly_zero___at___00Hex_DensePoly_monomial___at___00Hex_OrderedFnBench_prepThird_spec__4_spec__9_spec__22_spec__41_spec__61___closed__0_once>
  b8716e:	cmp    $0x1,%eax
  b87171:	jne    b8721b <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0xfb>
  b87177:	mov    0x40f4472(%rip),%r12        # 4c7b5f0 <lp_Hex_Hex_DensePoly_trimTrailingZerosGo___at___00Hex_DensePoly_trimTrailingZerosImpl___at___00Hex_DensePoly_ofCoeffs___at___00Hex_DensePoly_zero___at___00Hex_DensePoly_monomial___at___00Hex_OrderedFnBench_prepThird_spec__4_spec__9_spec__22_spec__41_spec__61___closed__0>
  b8717e:	mov    %rbp,%r14
  b87181:	shr    $1,%r14
  b87184:	mov    0x18(%rbx,%r14,8),%r13
  b87189:	mov    0x40f44e9(%rip),%eax        # 4c7b678 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5___closed__0_once>
  b8718f:	cmp    $0x1,%eax
  b87192:	jne    b8723d <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x11d>
  b87198:	mov    0x40f44d1(%rip),%rax        # 4c7b670 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5___closed__0>
  b8719f:	cmp    %r13,%rax
  b871a2:	je     b871ba <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x9a>
  b871a4:	mov    %r15,%rdi
  b871a7:	mov    %r13,%rsi
  b871aa:	mov    %r12,%rdx
  b871ad:	call   bbe9f0 <lp_Hex_Hex_RationalFn_instDecidableEq___redArg>
  b871b2:	test   %al,%al
  b871b4:	je     b872b9 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x199>
  b871ba:	test   $0x1,%bpl
  b871be:	je     b87265 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x145>
  b871c4:	inc    %r14
  b871c7:	js     b87287 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x167>
  b871cd:	lea    0x1(,%r14,2),%rsi
  b871d5:	jmp    b87130 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x10>
  b871da:	mov    %rbp,%rdi
  b871dd:	call   49a1c60 <lean_nat_big_lt>
  b871e2:	test   %al,%al
  b871e4:	jne    b87152 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x32>
  b871ea:	jmp    b872d5 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x1b5>
  b871ef:	lea    0x40f435a(%rip),%rdi        # 4c7b550 <lp_Hex_Hex_DensePoly_trimTrailingZerosGo___at___00Hex_DensePoly_trimTrailingZerosImpl___at___00Hex_DensePoly_ofCoeffs___at___00Hex_DensePoly_zero___at___00Hex_DensePoly_monomial___at___00Hex_OrderedFnBench_prepSecond_spec__1_spec__1_spec__2_spec__5_spec__6___closed__1>
  b871f6:	lea    0x40f435b(%rip),%rsi        # 4c7b558 <lp_Hex_Hex_DensePoly_trimTrailingZerosGo___at___00Hex_DensePoly_trimTrailingZerosImpl___at___00Hex_DensePoly_ofCoeffs___at___00Hex_DensePoly_zero___at___00Hex_DensePoly_monomial___at___00Hex_OrderedFnBench_prepSecond_spec__1_spec__1_spec__2_spec__5_spec__6___closed__1_once>
  b871fd:	lea    -0x1f964(%rip),%rdx        # b678a0 <_init_lp_Hex_Hex_DensePoly_trimTrailingZerosGo___at___00Hex_DensePoly_trimTrailingZerosImpl___at___00Hex_DensePoly_ofCoeffs___at___00Hex_DensePoly_zero___at___00Hex_DensePoly_monomial___at___00Hex_OrderedFnBench_prepSecond_spec__1_spec__1_spec__2_spec__5_spec__6___closed__1>
  b87204:	call   49a7cc0 <lean_obj_once_cold>
  b87209:	mov    %rax,%r15
  b8720c:	mov    0x40f43e6(%rip),%eax        # 4c7b5f8 <lp_Hex_Hex_DensePoly_trimTrailingZerosGo___at___00Hex_DensePoly_trimTrailingZerosImpl___at___00Hex_DensePoly_ofCoeffs___at___00Hex_DensePoly_zero___at___00Hex_DensePoly_monomial___at___00Hex_OrderedFnBench_prepThird_spec__4_spec__9_spec__22_spec__41_spec__61___closed__0_once>
  b87212:	cmp    $0x1,%eax
  b87215:	je     b87177 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x57>
  b8721b:	lea    0x40f43ce(%rip),%rdi        # 4c7b5f0 <lp_Hex_Hex_DensePoly_trimTrailingZerosGo___at___00Hex_DensePoly_trimTrailingZerosImpl___at___00Hex_DensePoly_ofCoeffs___at___00Hex_DensePoly_zero___at___00Hex_DensePoly_monomial___at___00Hex_OrderedFnBench_prepThird_spec__4_spec__9_spec__22_spec__41_spec__61___closed__0>
  b87222:	lea    0x40f43cf(%rip),%rsi        # 4c7b5f8 <lp_Hex_Hex_DensePoly_trimTrailingZerosGo___at___00Hex_DensePoly_trimTrailingZerosImpl___at___00Hex_DensePoly_ofCoeffs___at___00Hex_DensePoly_zero___at___00Hex_DensePoly_monomial___at___00Hex_OrderedFnBench_prepThird_spec__4_spec__9_spec__22_spec__41_spec__61___closed__0_once>
  b87229:	lea    -0x1da30(%rip),%rdx        # b69800 <_init_lp_Hex_Hex_DensePoly_trimTrailingZerosGo___at___00Hex_DensePoly_trimTrailingZerosImpl___at___00Hex_DensePoly_ofCoeffs___at___00Hex_DensePoly_zero___at___00Hex_DensePoly_monomial___at___00Hex_OrderedFnBench_prepThird_spec__4_spec__9_spec__22_spec__41_spec__61___closed__0>
  b87230:	call   49a7cc0 <lean_obj_once_cold>
  b87235:	mov    %rax,%r12
  b87238:	jmp    b8717e <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x5e>
  b8723d:	lea    0x40f442c(%rip),%rdi        # 4c7b670 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5___closed__0>
  b87244:	lea    0x40f442d(%rip),%rsi        # 4c7b678 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5___closed__0_once>
  b8724b:	lea    0xbe(%rip),%rdx        # b87310 <_init_lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5___closed__0>
  b87252:	call   49a8120 <lean_usize_once_cold>
  b87257:	cmp    %r13,%rax
  b8725a:	jne    b871a4 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x84>
  b87260:	jmp    b871ba <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x9a>
  b87265:	mov    $0x3,%esi
  b8726a:	mov    %rbp,%rdi
  b8726d:	call   49a0e70 <lean_nat_big_add>
  b87272:	mov    %rax,%rsi
  b87275:	mov    0x0(%rbp),%eax
  b87278:	cmp    $0x2,%eax
  b8727b:	jl     b8729e <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x17e>
  b8727d:	dec    %eax
  b8727f:	mov    %eax,0x0(%rbp)
  b87282:	jmp    b87130 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x10>
  b87287:	movabs $0x8000000000000000,%rdi
  b87291:	call   49a0cd0 <lean_big_usize_to_nat>
  b87296:	mov    %rax,%rsi
  b87299:	jmp    b87130 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x10>
  b8729e:	test   %eax,%eax
  b872a0:	je     b87130 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x10>
  b872a6:	mov    %rbp,%rdi
  b872a9:	mov    %rsi,%r14
  b872ac:	call   499e7b0 <lean_dec_ref_cold>
  b872b1:	mov    %r14,%rsi
  b872b4:	jmp    b87130 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x10>
  b872b9:	mov    $0x10,%edi
  b872be:	call   4a07de0 <lean_alloc_small_object_core>
  b872c3:	movl   $0x1,(%rax)
  b872c9:	movw   $0x101,0x6(%rax)
  b872cf:	mov    %rbp,0x8(%rax)
  b872d3:	jmp    b872e7 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x1c7>
  b872d5:	mov    0x0(%rbp),%eax
  b872d8:	cmp    $0x2,%eax
  b872db:	jl     b872f6 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x1d6>
  b872dd:	dec    %eax
  b872df:	mov    %eax,0x0(%rbp)
  b872e2:	mov    $0x1,%eax
  b872e7:	add    $0x8,%rsp
  b872eb:	pop    %rbx
  b872ec:	pop    %r12
  b872ee:	pop    %r13
  b872f0:	pop    %r14
  b872f2:	pop    %r15
  b872f4:	pop    %rbp
  b872f5:	ret
  b872f6:	test   %eax,%eax
  b872f8:	je     b872e2 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x1c2>
  b872fa:	mov    %rbp,%rdi
  b872fd:	call   499e7b0 <lean_dec_ref_cold>
  b87302:	jmp    b872e2 <lp_Hex_Array_findIdx_x3f_loop___at___00Hex_OrderedFn_Infinitesimal_lowestIndexImpl___at___00Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_sign___at___00Hex_OrderedFnBench_third_spec__0_spec__1_spec__3_spec__5+0x1c2>

Disassembly of section .init:

Disassembly of section .fini:

Disassembly of section .plt:
