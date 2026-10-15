
.lake/build/bin/hexorderedfn_bench:     file format elf64-x86-64


Disassembly of section .text:

0000000000b870a0 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0>:
  b870a0:	push   %r15
  b870a2:	push   %r14
  b870a4:	push   %rbx
  b870a5:	mov    %rdi,%r14
  b870a8:	mov    0x8(%rsi),%rdi
  b870ac:	mov    0x8(%rdi),%rax
  b870b0:	shl    $1,%rax
  b870b3:	test   %rax,%rax
  b870b6:	je     b8712b <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x8b>
  b870b8:	mov    0x10(%rsi),%r15
  b870bc:	call   b86fe0 <lp_Hex_Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0_spec__1>
  b870c1:	mov    (%r14),%ecx
  b870c4:	test   %ecx,%ecx
  b870c6:	jle    b87158 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0xb8>
  b870cc:	inc    %ecx
  b870ce:	mov    %ecx,(%r14)
  b870d1:	mov    %r14,%rdi
  b870d4:	mov    %rax,%rsi
  b870d7:	call   49aa010 <lean_apply_1>
  b870dc:	mov    %rax,%rbx
  b870df:	mov    %r15,%rdi
  b870e2:	call   b86fe0 <lp_Hex_Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0_spec__1>
  b870e7:	mov    %r14,%rdi
  b870ea:	mov    %rax,%rsi
  b870ed:	call   49aa010 <lean_apply_1>
  b870f2:	test   $0x1,%bl
  b870f5:	je     b8716d <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0xcd>
  b870f7:	test   $0x1,%al
  b870f9:	je     b87186 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0xe6>
  b870ff:	shr    $1,%rbx
  b87102:	movslq %ebx,%rcx
  b87105:	shr    $1,%rax
  b87108:	movslq %eax,%rdi
  b8710b:	imul   %rcx,%rdi
  b8710f:	movslq %edi,%rax
  b87112:	cmp    %rdi,%rax
  b87115:	jne    b871bb <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x11b>
  b8711b:	mov    %edi,%eax
  b8711d:	lea    0x1(,%rax,2),%rax
  b87125:	pop    %rbx
  b87126:	pop    %r14
  b87128:	pop    %r15
  b8712a:	ret
  b8712b:	mov    (%r14),%eax
  b8712e:	cmp    $0x2,%eax
  b87131:	jl     b871c5 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x125>
  b87137:	dec    %eax
  b87139:	mov    %eax,(%r14)
  b8713c:	mov    0x40f3a26(%rip),%eax        # 4c7ab68 <lp_Hex_Hex_OrderedFn_orderSign___at___00Hex_OrderedFnBench_scan_spec__0___closed__1_once>
  b87142:	cmp    $0x1,%eax
  b87145:	jne    b871da <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x13a>
  b8714b:	mov    0x40f3a0e(%rip),%rax        # 4c7ab60 <lp_Hex_Hex_OrderedFn_orderSign___at___00Hex_OrderedFnBench_scan_spec__0___closed__1>
  b87152:	pop    %rbx
  b87153:	pop    %r14
  b87155:	pop    %r15
  b87157:	ret
  b87158:	cmp    $0x90000001,%ecx
  b8715e:	jb     b870d1 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x31>
  b87164:	lock decl (%r14)
  b87168:	jmp    b870d1 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x31>
  b8716d:	mov    %rbx,%rdi
  b87170:	mov    %rax,%rsi
  b87173:	mov    %rax,%r15
  b87176:	call   49a2de0 <lean_int_big_mul>
  b8717b:	mov    %r15,%r14
  b8717e:	test   $0x1,%r15b
  b87182:	je     b87194 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0xf4>
  b87184:	jmp    b871aa <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x10a>
  b87186:	mov    %rbx,%rdi
  b87189:	mov    %rax,%r14
  b8718c:	mov    %rax,%rsi
  b8718f:	call   49a2de0 <lean_int_big_mul>
  b87194:	mov    (%r14),%ecx
  b87197:	cmp    $0x2,%ecx
  b8719a:	jl     b871f9 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x159>
  b8719c:	dec    %ecx
  b8719e:	mov    %ecx,(%r14)
  b871a1:	test   $0x1,%bl
  b871a4:	jne    b87125 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x85>
  b871aa:	mov    (%rbx),%ecx
  b871ac:	cmp    $0x2,%ecx
  b871af:	jl     b8720d <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x16d>
  b871b1:	dec    %ecx
  b871b3:	mov    %ecx,(%rbx)
  b871b5:	pop    %rbx
  b871b6:	pop    %r14
  b871b8:	pop    %r15
  b871ba:	ret
  b871bb:	pop    %rbx
  b871bc:	pop    %r14
  b871be:	pop    %r15
  b871c0:	jmp    49a2700 <lean_big_int64_to_int>
  b871c5:	test   %eax,%eax
  b871c7:	je     b8713c <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x9c>
  b871cd:	mov    %r14,%rdi
  b871d0:	call   499de30 <lean_dec_ref_cold>
  b871d5:	jmp    b8713c <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x9c>
  b871da:	lea    0x40f397f(%rip),%rdi        # 4c7ab60 <lp_Hex_Hex_OrderedFn_orderSign___at___00Hex_OrderedFnBench_scan_spec__0___closed__1>
  b871e1:	lea    0x40f3980(%rip),%rsi        # 4c7ab68 <lp_Hex_Hex_OrderedFn_orderSign___at___00Hex_OrderedFnBench_scan_spec__0___closed__1_once>
  b871e8:	lea    -0x23b67(%rip),%rdx        # b63688 <_init_lp_Hex_Hex_OrderedFn_orderSign___at___00Hex_OrderedFnBench_scan_spec__0___closed__1>
  b871ef:	pop    %rbx
  b871f0:	pop    %r14
  b871f2:	pop    %r15
  b871f4:	jmp    49a7340 <lean_obj_once_cold>
  b871f9:	test   %ecx,%ecx
  b871fb:	je     b871a1 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x101>
  b871fd:	mov    %r14,%rdi
  b87200:	mov    %rax,%r14
  b87203:	call   499de30 <lean_dec_ref_cold>
  b87208:	mov    %r14,%rax
  b8720b:	jmp    b871a1 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x101>
  b8720d:	mov    %rax,%r14
  b87210:	test   %ecx,%ecx
  b87212:	je     b8721c <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_third_spec__0+0x17c>
  b87214:	mov    %rbx,%rdi
  b87217:	call   499de30 <lean_dec_ref_cold>
  b8721c:	mov    %r14,%rax
  b8721f:	pop    %rbx
  b87220:	pop    %r14
  b87222:	pop    %r15
  b87224:	ret

Disassembly of section .init:

Disassembly of section .fini:

Disassembly of section .plt:
