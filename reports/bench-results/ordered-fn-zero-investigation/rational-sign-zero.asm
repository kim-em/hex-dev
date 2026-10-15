
.lake/build/bin/hexorderedfn_bench:     file format elf64-x86-64


Disassembly of section .text:

0000000000b63a30 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1>:
  b63a30:	push   %r15
  b63a32:	push   %r14
  b63a34:	push   %rbx
  b63a35:	mov    %rdi,%r14
  b63a38:	mov    0x8(%rsi),%rdi
  b63a3c:	mov    0x8(%rdi),%rax
  b63a40:	shl    $1,%rax
  b63a43:	test   %rax,%rax
  b63a46:	je     b63abb <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x8b>
  b63a48:	mov    0x10(%rsi),%r15
  b63a4c:	call   b63970 <lp_Hex_Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1_spec__2>
  b63a51:	mov    (%r14),%ecx
  b63a54:	test   %ecx,%ecx
  b63a56:	jle    b63ae8 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0xb8>
  b63a5c:	inc    %ecx
  b63a5e:	mov    %ecx,(%r14)
  b63a61:	mov    %r14,%rdi
  b63a64:	mov    %rax,%rsi
  b63a67:	call   49aa010 <lean_apply_1>
  b63a6c:	mov    %rax,%rbx
  b63a6f:	mov    %r15,%rdi
  b63a72:	call   b63970 <lp_Hex_Hex_OrderedFn_Infinitesimal_lowestCoeff___at___00Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1_spec__2>
  b63a77:	mov    %r14,%rdi
  b63a7a:	mov    %rax,%rsi
  b63a7d:	call   49aa010 <lean_apply_1>
  b63a82:	test   $0x1,%bl
  b63a85:	je     b63afd <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0xcd>
  b63a87:	test   $0x1,%al
  b63a89:	je     b63b16 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0xe6>
  b63a8f:	shr    $1,%rbx
  b63a92:	movslq %ebx,%rcx
  b63a95:	shr    $1,%rax
  b63a98:	movslq %eax,%rdi
  b63a9b:	imul   %rcx,%rdi
  b63a9f:	movslq %edi,%rax
  b63aa2:	cmp    %rdi,%rax
  b63aa5:	jne    b63b4b <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x11b>
  b63aab:	mov    %edi,%eax
  b63aad:	lea    0x1(,%rax,2),%rax
  b63ab5:	pop    %rbx
  b63ab6:	pop    %r14
  b63ab8:	pop    %r15
  b63aba:	ret
  b63abb:	mov    (%r14),%eax
  b63abe:	cmp    $0x2,%eax
  b63ac1:	jl     b63b55 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x125>
  b63ac7:	dec    %eax
  b63ac9:	mov    %eax,(%r14)
  b63acc:	mov    0x4117096(%rip),%eax        # 4c7ab68 <lp_Hex_Hex_OrderedFn_orderSign___at___00Hex_OrderedFnBench_scan_spec__0___closed__1_once>
  b63ad2:	cmp    $0x1,%eax
  b63ad5:	jne    b63b6a <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x13a>
  b63adb:	mov    0x411707e(%rip),%rax        # 4c7ab60 <lp_Hex_Hex_OrderedFn_orderSign___at___00Hex_OrderedFnBench_scan_spec__0___closed__1>
  b63ae2:	pop    %rbx
  b63ae3:	pop    %r14
  b63ae5:	pop    %r15
  b63ae7:	ret
  b63ae8:	cmp    $0x90000001,%ecx
  b63aee:	jb     b63a61 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x31>
  b63af4:	lock decl (%r14)
  b63af8:	jmp    b63a61 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x31>
  b63afd:	mov    %rbx,%rdi
  b63b00:	mov    %rax,%rsi
  b63b03:	mov    %rax,%r15
  b63b06:	call   49a2de0 <lean_int_big_mul>
  b63b0b:	mov    %r15,%r14
  b63b0e:	test   $0x1,%r15b
  b63b12:	je     b63b24 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0xf4>
  b63b14:	jmp    b63b3a <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x10a>
  b63b16:	mov    %rbx,%rdi
  b63b19:	mov    %rax,%r14
  b63b1c:	mov    %rax,%rsi
  b63b1f:	call   49a2de0 <lean_int_big_mul>
  b63b24:	mov    (%r14),%ecx
  b63b27:	cmp    $0x2,%ecx
  b63b2a:	jl     b63b89 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x159>
  b63b2c:	dec    %ecx
  b63b2e:	mov    %ecx,(%r14)
  b63b31:	test   $0x1,%bl
  b63b34:	jne    b63ab5 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x85>
  b63b3a:	mov    (%rbx),%ecx
  b63b3c:	cmp    $0x2,%ecx
  b63b3f:	jl     b63b9d <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x16d>
  b63b41:	dec    %ecx
  b63b43:	mov    %ecx,(%rbx)
  b63b45:	pop    %rbx
  b63b46:	pop    %r14
  b63b48:	pop    %r15
  b63b4a:	ret
  b63b4b:	pop    %rbx
  b63b4c:	pop    %r14
  b63b4e:	pop    %r15
  b63b50:	jmp    49a2700 <lean_big_int64_to_int>
  b63b55:	test   %eax,%eax
  b63b57:	je     b63acc <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x9c>
  b63b5d:	mov    %r14,%rdi
  b63b60:	call   499de30 <lean_dec_ref_cold>
  b63b65:	jmp    b63acc <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x9c>
  b63b6a:	lea    0x4116fef(%rip),%rdi        # 4c7ab60 <lp_Hex_Hex_OrderedFn_orderSign___at___00Hex_OrderedFnBench_scan_spec__0___closed__1>
  b63b71:	lea    0x4116ff0(%rip),%rsi        # 4c7ab68 <lp_Hex_Hex_OrderedFn_orderSign___at___00Hex_OrderedFnBench_scan_spec__0___closed__1_once>
  b63b78:	lea    -0x4f7(%rip),%rdx        # b63688 <_init_lp_Hex_Hex_OrderedFn_orderSign___at___00Hex_OrderedFnBench_scan_spec__0___closed__1>
  b63b7f:	pop    %rbx
  b63b80:	pop    %r14
  b63b82:	pop    %r15
  b63b84:	jmp    49a7340 <lean_obj_once_cold>
  b63b89:	test   %ecx,%ecx
  b63b8b:	je     b63b31 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x101>
  b63b8d:	mov    %r14,%rdi
  b63b90:	mov    %rax,%r14
  b63b93:	call   499de30 <lean_dec_ref_cold>
  b63b98:	mov    %r14,%rax
  b63b9b:	jmp    b63b31 <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x101>
  b63b9d:	mov    %rax,%r14
  b63ba0:	test   %ecx,%ecx
  b63ba2:	je     b63bac <lp_Hex_Hex_OrderedFn_Infinitesimal_signImpl___at___00Hex_OrderedFnBench_scan_spec__1+0x17c>
  b63ba4:	mov    %rbx,%rdi
  b63ba7:	call   499de30 <lean_dec_ref_cold>
  b63bac:	mov    %r14,%rax
  b63baf:	pop    %rbx
  b63bb0:	pop    %r14
  b63bb2:	pop    %r15
  b63bb4:	ret

Disassembly of section .init:

Disassembly of section .fini:

Disassembly of section .plt:
