
/home/kim/worktrees/hex-dev/hex-dev-issue-10377-allocation/.lake/build/bin/hexsigndet_bench:     file format elf64-x86-64


Disassembly of section .text:

0000000004a1f720 <__gmp_tmp_reentrant_alloc>:
 4a1f720:	55                   	push   %rbp
 4a1f721:	53                   	push   %rbx
 4a1f722:	48 8d 5e 10          	lea    0x10(%rsi),%rbx
 4a1f726:	48 89 fd             	mov    %rdi,%rbp
 4a1f729:	48 83 ec 08          	sub    $0x8,%rsp
 4a1f72d:	48 8d 05 ec 4e 30 00 	lea    0x304eec(%rip),%rax        # 4d24620 <__gmp_allocate_func>
 4a1f734:	48 89 df             	mov    %rbx,%rdi
 4a1f737:	ff 10                	call   *(%rax)
 4a1f739:	48 8b 55 00          	mov    0x0(%rbp),%rdx
 4a1f73d:	48 89 58 08          	mov    %rbx,0x8(%rax)
 4a1f741:	48 89 10             	mov    %rdx,(%rax)
 4a1f744:	48 89 45 00          	mov    %rax,0x0(%rbp)
 4a1f748:	48 83 c4 08          	add    $0x8,%rsp
 4a1f74c:	48 83 c0 10          	add    $0x10,%rax
 4a1f750:	5b                   	pop    %rbx
 4a1f751:	5d                   	pop    %rbp
 4a1f752:	c3                   	ret

Disassembly of section .init:

Disassembly of section .fini:

Disassembly of section .plt:
