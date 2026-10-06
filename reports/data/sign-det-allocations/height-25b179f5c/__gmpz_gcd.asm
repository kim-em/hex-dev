
/home/kim/worktrees/hex-dev/hex-dev-issue-10377-allocation/.lake/build/bin/hexsigndet_bench:     file format elf64-x86-64


Disassembly of section .text:

0000000004a4b790 <__gmpz_gcd>:
 4a4b790:	55                   	push   %rbp
 4a4b791:	48 89 e5             	mov    %rsp,%rbp
 4a4b794:	41 57                	push   %r15
 4a4b796:	41 56                	push   %r14
 4a4b798:	41 55                	push   %r13
 4a4b79a:	41 54                	push   %r12
 4a4b79c:	53                   	push   %rbx
 4a4b79d:	48 89 fb             	mov    %rdi,%rbx
 4a4b7a0:	48 83 ec 58          	sub    $0x58,%rsp
 4a4b7a4:	8b 7e 04             	mov    0x4(%rsi),%edi
 4a4b7a7:	8b 4a 04             	mov    0x4(%rdx),%ecx
 4a4b7aa:	64 48 8b 04 25 28 00 	mov    %fs:0x28,%rax
 4a4b7b1:	00 00 
 4a4b7b3:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
 4a4b7b7:	31 c0                	xor    %eax,%eax
 4a4b7b9:	8b 46 04             	mov    0x4(%rsi),%eax
 4a4b7bc:	4c 8b 62 08          	mov    0x8(%rdx),%r12
 4a4b7c0:	c1 f8 1f             	sar    $0x1f,%eax
 4a4b7c3:	31 c7                	xor    %eax,%edi
 4a4b7c5:	29 c7                	sub    %eax,%edi
 4a4b7c7:	8b 42 04             	mov    0x4(%rdx),%eax
 4a4b7ca:	4c 63 ef             	movslq %edi,%r13
 4a4b7cd:	c1 f8 1f             	sar    $0x1f,%eax
 4a4b7d0:	31 c1                	xor    %eax,%ecx
 4a4b7d2:	29 c1                	sub    %eax,%ecx
 4a4b7d4:	4d 85 ed             	test   %r13,%r13
 4a4b7d7:	4c 63 f1             	movslq %ecx,%r14
 4a4b7da:	75 4c                	jne    4a4b828 <__gmpz_gcd+0x98>
 4a4b7dc:	48 39 da             	cmp    %rbx,%rdx
 4a4b7df:	89 4b 04             	mov    %ecx,0x4(%rbx)
 4a4b7e2:	74 1c                	je     4a4b800 <__gmpz_gcd+0x70>
 4a4b7e4:	3b 0b                	cmp    (%rbx),%ecx
 4a4b7e6:	0f 8f 54 04 00 00    	jg     4a4bc40 <__gmpz_gcd+0x4b0>
 4a4b7ec:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
 4a4b7f0:	48 8d 05 c9 8c 2d 00 	lea    0x2d8cc9(%rip),%rax        # 4d244c0 <__gmpn_cpuvec>
 4a4b7f7:	4c 89 f2             	mov    %r14,%rdx
 4a4b7fa:	4c 89 e6             	mov    %r12,%rsi
 4a4b7fd:	ff 50 50             	call   *0x50(%rax)
 4a4b800:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
 4a4b804:	64 48 33 04 25 28 00 	xor    %fs:0x28,%rax
 4a4b80b:	00 00 
 4a4b80d:	0f 85 fb 04 00 00    	jne    4a4bd0e <__gmpz_gcd+0x57e>
 4a4b813:	48 8d 65 d8          	lea    -0x28(%rbp),%rsp
 4a4b817:	5b                   	pop    %rbx
 4a4b818:	41 5c                	pop    %r12
 4a4b81a:	41 5d                	pop    %r13
 4a4b81c:	41 5e                	pop    %r14
 4a4b81e:	41 5f                	pop    %r15
 4a4b820:	5d                   	pop    %rbp
 4a4b821:	c3                   	ret
 4a4b822:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
 4a4b828:	4d 85 f6             	test   %r14,%r14
 4a4b82b:	4c 8b 7e 08          	mov    0x8(%rsi),%r15
 4a4b82f:	75 2f                	jne    4a4b860 <__gmpz_gcd+0xd0>
 4a4b831:	48 39 de             	cmp    %rbx,%rsi
 4a4b834:	89 7b 04             	mov    %edi,0x4(%rbx)
 4a4b837:	74 c7                	je     4a4b800 <__gmpz_gcd+0x70>
 4a4b839:	3b 3b                	cmp    (%rbx),%edi
 4a4b83b:	0f 8f 17 04 00 00    	jg     4a4bc58 <__gmpz_gcd+0x4c8>
 4a4b841:	48 8b 7b 08          	mov    0x8(%rbx),%rdi
 4a4b845:	48 8d 05 74 8c 2d 00 	lea    0x2d8c74(%rip),%rax        # 4d244c0 <__gmpn_cpuvec>
 4a4b84c:	4c 89 ea             	mov    %r13,%rdx
 4a4b84f:	4c 89 fe             	mov    %r15,%rsi
 4a4b852:	ff 50 50             	call   *0x50(%rax)
 4a4b855:	eb a9                	jmp    4a4b800 <__gmpz_gcd+0x70>
 4a4b857:	66 0f 1f 84 00 00 00 	nopw   0x0(%rax,%rax,1)
 4a4b85e:	00 00 
 4a4b860:	49 83 fd 01          	cmp    $0x1,%r13
 4a4b864:	0f 84 56 02 00 00    	je     4a4bac0 <__gmpz_gcd+0x330>
 4a4b86a:	49 83 fe 01          	cmp    $0x1,%r14
 4a4b86e:	0f 84 7c 02 00 00    	je     4a4baf0 <__gmpz_gcd+0x360>
 4a4b874:	49 8b 07             	mov    (%r15),%rax
 4a4b877:	48 c7 45 c0 00 00 00 	movq   $0x0,-0x40(%rbp)
 4a4b87e:	00 
 4a4b87f:	4c 89 fa             	mov    %r15,%rdx
 4a4b882:	48 85 c0             	test   %rax,%rax
 4a4b885:	0f 85 e5 03 00 00    	jne    4a4bc70 <__gmpz_gcd+0x4e0>
 4a4b88b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
 4a4b890:	49 83 c7 08          	add    $0x8,%r15
 4a4b894:	49 8b 07             	mov    (%r15),%rax
 4a4b897:	48 85 c0             	test   %rax,%rax
 4a4b89a:	74 f4                	je     4a4b890 <__gmpz_gcd+0x100>
 4a4b89c:	4c 89 fe             	mov    %r15,%rsi
 4a4b89f:	48 29 d6             	sub    %rdx,%rsi
 4a4b8a2:	48 89 f2             	mov    %rsi,%rdx
 4a4b8a5:	48 c1 fa 03          	sar    $0x3,%rdx
 4a4b8a9:	48 89 55 98          	mov    %rdx,-0x68(%rbp)
 4a4b8ad:	49 29 d5             	sub    %rdx,%r13
 4a4b8b0:	4e 8d 04 ed 00 00 00 	lea    0x0(,%r13,8),%r8
 4a4b8b7:	00 
 4a4b8b8:	48 0f bc c0          	bsf    %rax,%rax
 4a4b8bc:	49 81 f8 00 7f 00 00 	cmp    $0x7f00,%r8
 4a4b8c3:	48 89 45 a0          	mov    %rax,-0x60(%rbp)
 4a4b8c7:	0f 87 c3 03 00 00    	ja     4a4bc90 <__gmpz_gcd+0x500>
 4a4b8cd:	49 8d 40 1e          	lea    0x1e(%r8),%rax
 4a4b8d1:	48 83 e0 f0          	and    $0xfffffffffffffff0,%rax
 4a4b8d5:	48 29 c4             	sub    %rax,%rsp
 4a4b8d8:	48 8d 44 24 0f       	lea    0xf(%rsp),%rax
 4a4b8dd:	48 83 e0 f0          	and    $0xfffffffffffffff0,%rax
 4a4b8e1:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
 4a4b8e5:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
 4a4b8e9:	4c 89 45 a8          	mov    %r8,-0x58(%rbp)
 4a4b8ed:	48 85 c0             	test   %rax,%rax
 4a4b8f0:	0f 84 6a 02 00 00    	je     4a4bb60 <__gmpz_gcd+0x3d0>
 4a4b8f6:	4c 8d 0d c3 8b 2d 00 	lea    0x2d8bc3(%rip),%r9        # 4d244c0 <__gmpn_cpuvec>
 4a4b8fd:	4c 89 fe             	mov    %r15,%rsi
 4a4b900:	4c 8b 7d b8          	mov    -0x48(%rbp),%r15
 4a4b904:	4c 89 ea             	mov    %r13,%rdx
 4a4b907:	89 c1                	mov    %eax,%ecx
 4a4b909:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
 4a4b90d:	4c 89 ff             	mov    %r15,%rdi
 4a4b910:	41 ff 91 00 01 00 00 	call   *0x100(%r9)
 4a4b917:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
 4a4b91b:	4b 83 7c 07 f8 00    	cmpq   $0x0,-0x8(%r15,%r8,1)
 4a4b921:	0f 94 c0             	sete   %al
 4a4b924:	0f b6 c0             	movzbl %al,%eax
 4a4b927:	49 29 c5             	sub    %rax,%r13
 4a4b92a:	4d 8b 04 24          	mov    (%r12),%r8
 4a4b92e:	4c 89 e0             	mov    %r12,%rax
 4a4b931:	4d 85 c0             	test   %r8,%r8
 4a4b934:	0f 85 46 03 00 00    	jne    4a4bc80 <__gmpz_gcd+0x4f0>
 4a4b93a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
 4a4b940:	49 83 c4 08          	add    $0x8,%r12
 4a4b944:	4d 8b 04 24          	mov    (%r12),%r8
 4a4b948:	4d 85 c0             	test   %r8,%r8
 4a4b94b:	74 f3                	je     4a4b940 <__gmpz_gcd+0x1b0>
 4a4b94d:	4d 89 e2             	mov    %r12,%r10
 4a4b950:	49 29 c2             	sub    %rax,%r10
 4a4b953:	49 c1 fa 03          	sar    $0x3,%r10
 4a4b957:	4d 89 d7             	mov    %r10,%r15
 4a4b95a:	4d 29 d6             	sub    %r10,%r14
 4a4b95d:	4e 8d 0c f5 00 00 00 	lea    0x0(,%r14,8),%r9
 4a4b964:	00 
 4a4b965:	4d 0f bc c0          	bsf    %r8,%r8
 4a4b969:	49 81 f9 00 7f 00 00 	cmp    $0x7f00,%r9
 4a4b970:	4c 89 45 a8          	mov    %r8,-0x58(%rbp)
 4a4b974:	0f 87 36 03 00 00    	ja     4a4bcb0 <__gmpz_gcd+0x520>
 4a4b97a:	49 8d 41 1e          	lea    0x1e(%r9),%rax
 4a4b97e:	48 83 e0 f0          	and    $0xfffffffffffffff0,%rax
 4a4b982:	48 29 c4             	sub    %rax,%rsp
 4a4b985:	4c 8d 5c 24 0f       	lea    0xf(%rsp),%r11
 4a4b98a:	49 83 e3 f0          	and    $0xfffffffffffffff0,%r11
 4a4b98e:	4d 85 c0             	test   %r8,%r8
 4a4b991:	4c 89 4d 90          	mov    %r9,-0x70(%rbp)
 4a4b995:	0f 84 9d 01 00 00    	je     4a4bb38 <__gmpz_gcd+0x3a8>
 4a4b99b:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
 4a4b99f:	44 89 c1             	mov    %r8d,%ecx
 4a4b9a2:	4c 89 45 80          	mov    %r8,-0x80(%rbp)
 4a4b9a6:	4c 89 f2             	mov    %r14,%rdx
 4a4b9a9:	4c 89 df             	mov    %r11,%rdi
 4a4b9ac:	4c 89 5d 88          	mov    %r11,-0x78(%rbp)
 4a4b9b0:	4c 89 e6             	mov    %r12,%rsi
 4a4b9b3:	ff 90 00 01 00 00    	call   *0x100(%rax)
 4a4b9b9:	4c 8b 5d 88          	mov    -0x78(%rbp),%r11
 4a4b9bd:	4c 8b 4d 90          	mov    -0x70(%rbp),%r9
 4a4b9c1:	31 c0                	xor    %eax,%eax
 4a4b9c3:	4c 8b 45 80          	mov    -0x80(%rbp),%r8
 4a4b9c7:	4b 83 7c 0b f8 00    	cmpq   $0x0,-0x8(%r11,%r9,1)
 4a4b9cd:	0f 94 c0             	sete   %al
 4a4b9d0:	49 29 c6             	sub    %rax,%r14
 4a4b9d3:	48 8b 45 98          	mov    -0x68(%rbp),%rax
 4a4b9d7:	49 39 c7             	cmp    %rax,%r15
 4a4b9da:	7c 12                	jl     4a4b9ee <__gmpz_gcd+0x25e>
 4a4b9dc:	0f 8e fe 01 00 00    	jle    4a4bbe0 <__gmpz_gcd+0x450>
 4a4b9e2:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
 4a4b9e6:	4c 8b 7d 98          	mov    -0x68(%rbp),%r15
 4a4b9ea:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
 4a4b9ee:	4d 39 f5             	cmp    %r14,%r13
 4a4b9f1:	0f 8c 29 01 00 00    	jl     4a4bb20 <__gmpz_gcd+0x390>
 4a4b9f7:	75 14                	jne    4a4ba0d <__gmpz_gcd+0x27d>
 4a4b9f9:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
 4a4b9fd:	4b 8b 74 eb f8       	mov    -0x8(%r11,%r13,8),%rsi
 4a4ba02:	4a 39 74 e8 f8       	cmp    %rsi,-0x8(%rax,%r13,8)
 4a4ba07:	0f 82 13 01 00 00    	jb     4a4bb20 <__gmpz_gcd+0x390>
 4a4ba0d:	48 8b 75 b8          	mov    -0x48(%rbp),%rsi
 4a4ba11:	4d 89 f0             	mov    %r14,%r8
 4a4ba14:	4c 89 d9             	mov    %r11,%rcx
 4a4ba17:	4c 89 ea             	mov    %r13,%rdx
 4a4ba1a:	4c 89 df             	mov    %r11,%rdi
 4a4ba1d:	4c 89 5d b8          	mov    %r11,-0x48(%rbp)
 4a4ba21:	e8 2a 03 00 00       	call   4a4bd50 <__gmpn_gcd>
 4a4ba26:	48 8b 75 a8          	mov    -0x58(%rbp),%rsi
 4a4ba2a:	48 89 c2             	mov    %rax,%rdx
 4a4ba2d:	4d 8d 24 07          	lea    (%r15,%rax,1),%r12
 4a4ba31:	4c 8b 5d b8          	mov    -0x48(%rbp),%r11
 4a4ba35:	48 63 03             	movslq (%rbx),%rax
 4a4ba38:	48 85 f6             	test   %rsi,%rsi
 4a4ba3b:	0f 84 3f 01 00 00    	je     4a4bb80 <__gmpz_gcd+0x3f0>
 4a4ba41:	4c 8d 2c d5 00 00 00 	lea    0x0(,%rdx,8),%r13
 4a4ba48:	00 
 4a4ba49:	b9 40 00 00 00       	mov    $0x40,%ecx
 4a4ba4e:	41 89 f0             	mov    %esi,%r8d
 4a4ba51:	29 f1                	sub    %esi,%ecx
 4a4ba53:	4b 8b 74 2b f8       	mov    -0x8(%r11,%r13,1),%rsi
 4a4ba58:	48 d3 ee             	shr    %cl,%rsi
 4a4ba5b:	48 85 f6             	test   %rsi,%rsi
 4a4ba5e:	0f 95 c1             	setne  %cl
 4a4ba61:	0f b6 c9             	movzbl %cl,%ecx
 4a4ba64:	49 01 cc             	add    %rcx,%r12
 4a4ba67:	4c 39 e0             	cmp    %r12,%rax
 4a4ba6a:	0f 8c 87 01 00 00    	jl     4a4bbf7 <__gmpz_gcd+0x467>
 4a4ba70:	48 8b 43 08          	mov    0x8(%rbx),%rax
 4a4ba74:	4d 85 ff             	test   %r15,%r15
 4a4ba77:	74 19                	je     4a4ba92 <__gmpz_gcd+0x302>
 4a4ba79:	4c 89 fe             	mov    %r15,%rsi
 4a4ba7c:	48 89 c1             	mov    %rax,%rcx
 4a4ba7f:	90                   	nop
 4a4ba80:	48 83 c1 08          	add    $0x8,%rcx
 4a4ba84:	48 83 ee 01          	sub    $0x1,%rsi
 4a4ba88:	48 c7 41 f8 00 00 00 	movq   $0x0,-0x8(%rcx)
 4a4ba8f:	00 
 4a4ba90:	75 ee                	jne    4a4ba80 <__gmpz_gcd+0x2f0>
 4a4ba92:	4e 8d 3c f8          	lea    (%rax,%r15,8),%r15
 4a4ba96:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
 4a4ba9a:	44 89 c1             	mov    %r8d,%ecx
 4a4ba9d:	4c 89 de             	mov    %r11,%rsi
 4a4baa0:	4c 89 ff             	mov    %r15,%rdi
 4a4baa3:	ff 50 70             	call   *0x70(%rax)
 4a4baa6:	48 85 c0             	test   %rax,%rax
 4a4baa9:	0f 84 11 01 00 00    	je     4a4bbc0 <__gmpz_gcd+0x430>
 4a4baaf:	4b 89 04 2f          	mov    %rax,(%r15,%r13,1)
 4a4bab3:	e9 08 01 00 00       	jmp    4a4bbc0 <__gmpz_gcd+0x430>
 4a4bab8:	0f 1f 84 00 00 00 00 	nopl   0x0(%rax,%rax,1)
 4a4babf:	00 
 4a4bac0:	8b 0b                	mov    (%rbx),%ecx
 4a4bac2:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
 4a4bac9:	49 8b 17             	mov    (%r15),%rdx
 4a4bacc:	85 c9                	test   %ecx,%ecx
 4a4bace:	0f 8e 00 02 00 00    	jle    4a4bcd4 <__gmpz_gcd+0x544>
 4a4bad4:	48 8b 5b 08          	mov    0x8(%rbx),%rbx
 4a4bad8:	4c 89 f6             	mov    %r14,%rsi
 4a4badb:	4c 89 e7             	mov    %r12,%rdi
 4a4bade:	e8 2d 08 00 00       	call   4a4c310 <__gmpn_gcd_1>
 4a4bae3:	48 89 03             	mov    %rax,(%rbx)
 4a4bae6:	e9 15 fd ff ff       	jmp    4a4b800 <__gmpz_gcd+0x70>
 4a4baeb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
 4a4baf0:	8b 03                	mov    (%rbx),%eax
 4a4baf2:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
 4a4baf9:	49 8b 14 24          	mov    (%r12),%rdx
 4a4bafd:	85 c0                	test   %eax,%eax
 4a4baff:	0f 8e ec 01 00 00    	jle    4a4bcf1 <__gmpz_gcd+0x561>
 4a4bb05:	48 8b 5b 08          	mov    0x8(%rbx),%rbx
 4a4bb09:	4c 89 ee             	mov    %r13,%rsi
 4a4bb0c:	4c 89 ff             	mov    %r15,%rdi
 4a4bb0f:	e8 fc 07 00 00       	call   4a4c310 <__gmpn_gcd_1>
 4a4bb14:	48 89 03             	mov    %rax,(%rbx)
 4a4bb17:	e9 e4 fc ff ff       	jmp    4a4b800 <__gmpz_gcd+0x70>
 4a4bb1c:	0f 1f 40 00          	nopl   0x0(%rax)
 4a4bb20:	4d 89 e8             	mov    %r13,%r8
 4a4bb23:	48 8b 4d b8          	mov    -0x48(%rbp),%rcx
 4a4bb27:	4c 89 f2             	mov    %r14,%rdx
 4a4bb2a:	4c 89 de             	mov    %r11,%rsi
 4a4bb2d:	e9 e8 fe ff ff       	jmp    4a4ba1a <__gmpz_gcd+0x28a>
 4a4bb32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
 4a4bb38:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
 4a4bb3c:	4c 89 45 88          	mov    %r8,-0x78(%rbp)
 4a4bb40:	4c 89 df             	mov    %r11,%rdi
 4a4bb43:	4c 89 5d 90          	mov    %r11,-0x70(%rbp)
 4a4bb47:	4c 89 f2             	mov    %r14,%rdx
 4a4bb4a:	4c 89 e6             	mov    %r12,%rsi
 4a4bb4d:	ff 50 50             	call   *0x50(%rax)
 4a4bb50:	4c 8b 45 88          	mov    -0x78(%rbp),%r8
 4a4bb54:	4c 8b 5d 90          	mov    -0x70(%rbp),%r11
 4a4bb58:	e9 76 fe ff ff       	jmp    4a4b9d3 <__gmpz_gcd+0x243>
 4a4bb5d:	0f 1f 00             	nopl   (%rax)
 4a4bb60:	48 8d 05 59 89 2d 00 	lea    0x2d8959(%rip),%rax        # 4d244c0 <__gmpn_cpuvec>
 4a4bb67:	4c 89 ea             	mov    %r13,%rdx
 4a4bb6a:	4c 89 fe             	mov    %r15,%rsi
 4a4bb6d:	48 8b 7d b8          	mov    -0x48(%rbp),%rdi
 4a4bb71:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
 4a4bb75:	ff 50 50             	call   *0x50(%rax)
 4a4bb78:	e9 ad fd ff ff       	jmp    4a4b92a <__gmpz_gcd+0x19a>
 4a4bb7d:	0f 1f 00             	nopl   (%rax)
 4a4bb80:	4c 39 e0             	cmp    %r12,%rax
 4a4bb83:	0f 8c 96 00 00 00    	jl     4a4bc1f <__gmpz_gcd+0x48f>
 4a4bb89:	48 8b 43 08          	mov    0x8(%rbx),%rax
 4a4bb8d:	4d 85 ff             	test   %r15,%r15
 4a4bb90:	74 20                	je     4a4bbb2 <__gmpz_gcd+0x422>
 4a4bb92:	4c 89 fe             	mov    %r15,%rsi
 4a4bb95:	48 89 c1             	mov    %rax,%rcx
 4a4bb98:	0f 1f 84 00 00 00 00 	nopl   0x0(%rax,%rax,1)
 4a4bb9f:	00 
 4a4bba0:	48 83 c1 08          	add    $0x8,%rcx
 4a4bba4:	48 83 ee 01          	sub    $0x1,%rsi
 4a4bba8:	48 c7 41 f8 00 00 00 	movq   $0x0,-0x8(%rcx)
 4a4bbaf:	00 
 4a4bbb0:	75 ee                	jne    4a4bba0 <__gmpz_gcd+0x410>
 4a4bbb2:	4a 8d 3c f8          	lea    (%rax,%r15,8),%rdi
 4a4bbb6:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
 4a4bbba:	4c 89 de             	mov    %r11,%rsi
 4a4bbbd:	ff 50 50             	call   *0x50(%rax)
 4a4bbc0:	48 8b 7d c0          	mov    -0x40(%rbp),%rdi
 4a4bbc4:	44 89 63 04          	mov    %r12d,0x4(%rbx)
 4a4bbc8:	48 85 ff             	test   %rdi,%rdi
 4a4bbcb:	0f 84 2f fc ff ff    	je     4a4b800 <__gmpz_gcd+0x70>
 4a4bbd1:	e8 8a 3b fd ff       	call   4a1f760 <__gmp_tmp_reentrant_free>
 4a4bbd6:	e9 25 fc ff ff       	jmp    4a4b800 <__gmpz_gcd+0x70>
 4a4bbdb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
 4a4bbe0:	48 8b 75 a0          	mov    -0x60(%rbp),%rsi
 4a4bbe4:	49 89 c7             	mov    %rax,%r15
 4a4bbe7:	49 39 f0             	cmp    %rsi,%r8
 4a4bbea:	4c 0f 47 c6          	cmova  %rsi,%r8
 4a4bbee:	4c 89 45 a8          	mov    %r8,-0x58(%rbp)
 4a4bbf2:	e9 f7 fd ff ff       	jmp    4a4b9ee <__gmpz_gcd+0x25e>
 4a4bbf7:	4c 89 e6             	mov    %r12,%rsi
 4a4bbfa:	48 89 df             	mov    %rbx,%rdi
 4a4bbfd:	48 89 55 a0          	mov    %rdx,-0x60(%rbp)
 4a4bc01:	4c 89 5d a8          	mov    %r11,-0x58(%rbp)
 4a4bc05:	44 89 45 b8          	mov    %r8d,-0x48(%rbp)
 4a4bc09:	e8 32 20 fd ff       	call   4a1dc40 <__gmpz_realloc>
 4a4bc0e:	44 8b 45 b8          	mov    -0x48(%rbp),%r8d
 4a4bc12:	4c 8b 5d a8          	mov    -0x58(%rbp),%r11
 4a4bc16:	48 8b 55 a0          	mov    -0x60(%rbp),%rdx
 4a4bc1a:	e9 55 fe ff ff       	jmp    4a4ba74 <__gmpz_gcd+0x2e4>
 4a4bc1f:	4c 89 e6             	mov    %r12,%rsi
 4a4bc22:	48 89 df             	mov    %rbx,%rdi
 4a4bc25:	48 89 55 a8          	mov    %rdx,-0x58(%rbp)
 4a4bc29:	4c 89 5d b8          	mov    %r11,-0x48(%rbp)
 4a4bc2d:	e8 0e 20 fd ff       	call   4a1dc40 <__gmpz_realloc>
 4a4bc32:	4c 8b 5d b8          	mov    -0x48(%rbp),%r11
 4a4bc36:	48 8b 55 a8          	mov    -0x58(%rbp),%rdx
 4a4bc3a:	e9 4e ff ff ff       	jmp    4a4bb8d <__gmpz_gcd+0x3fd>
 4a4bc3f:	90                   	nop
 4a4bc40:	48 89 df             	mov    %rbx,%rdi
 4a4bc43:	4c 89 f6             	mov    %r14,%rsi
 4a4bc46:	e8 f5 1f fd ff       	call   4a1dc40 <__gmpz_realloc>
 4a4bc4b:	48 89 c7             	mov    %rax,%rdi
 4a4bc4e:	e9 9d fb ff ff       	jmp    4a4b7f0 <__gmpz_gcd+0x60>
 4a4bc53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
 4a4bc58:	48 89 df             	mov    %rbx,%rdi
 4a4bc5b:	4c 89 ee             	mov    %r13,%rsi
 4a4bc5e:	e8 dd 1f fd ff       	call   4a1dc40 <__gmpz_realloc>
 4a4bc63:	48 89 c7             	mov    %rax,%rdi
 4a4bc66:	e9 da fb ff ff       	jmp    4a4b845 <__gmpz_gcd+0xb5>
 4a4bc6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
 4a4bc70:	48 c7 45 98 00 00 00 	movq   $0x0,-0x68(%rbp)
 4a4bc77:	00 
 4a4bc78:	e9 33 fc ff ff       	jmp    4a4b8b0 <__gmpz_gcd+0x120>
 4a4bc7d:	0f 1f 00             	nopl   (%rax)
 4a4bc80:	45 31 ff             	xor    %r15d,%r15d
 4a4bc83:	e9 d5 fc ff ff       	jmp    4a4b95d <__gmpz_gcd+0x1cd>
 4a4bc88:	0f 1f 84 00 00 00 00 	nopl   0x0(%rax,%rax,1)
 4a4bc8f:	00 
 4a4bc90:	48 8d 7d c0          	lea    -0x40(%rbp),%rdi
 4a4bc94:	4c 89 c6             	mov    %r8,%rsi
 4a4bc97:	4c 89 45 b0          	mov    %r8,-0x50(%rbp)
 4a4bc9b:	e8 80 3a fd ff       	call   4a1f720 <__gmp_tmp_reentrant_alloc>
 4a4bca0:	4c 8b 45 b0          	mov    -0x50(%rbp),%r8
 4a4bca4:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
 4a4bca8:	e9 38 fc ff ff       	jmp    4a4b8e5 <__gmpz_gcd+0x155>
 4a4bcad:	0f 1f 00             	nopl   (%rax)
 4a4bcb0:	48 8d 7d c0          	lea    -0x40(%rbp),%rdi
 4a4bcb4:	4c 89 ce             	mov    %r9,%rsi
 4a4bcb7:	4c 89 45 88          	mov    %r8,-0x78(%rbp)
 4a4bcbb:	4c 89 4d 90          	mov    %r9,-0x70(%rbp)
 4a4bcbf:	e8 5c 3a fd ff       	call   4a1f720 <__gmp_tmp_reentrant_alloc>
 4a4bcc4:	4c 8b 45 88          	mov    -0x78(%rbp),%r8
 4a4bcc8:	49 89 c3             	mov    %rax,%r11
 4a4bccb:	4c 8b 4d 90          	mov    -0x70(%rbp),%r9
 4a4bccf:	e9 ba fc ff ff       	jmp    4a4b98e <__gmpz_gcd+0x1fe>
 4a4bcd4:	48 89 df             	mov    %rbx,%rdi
 4a4bcd7:	be 01 00 00 00       	mov    $0x1,%esi
 4a4bcdc:	48 89 55 b8          	mov    %rdx,-0x48(%rbp)
 4a4bce0:	e8 5b 1f fd ff       	call   4a1dc40 <__gmpz_realloc>
 4a4bce5:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
 4a4bce9:	48 89 c3             	mov    %rax,%rbx
 4a4bcec:	e9 e7 fd ff ff       	jmp    4a4bad8 <__gmpz_gcd+0x348>
 4a4bcf1:	48 89 df             	mov    %rbx,%rdi
 4a4bcf4:	be 01 00 00 00       	mov    $0x1,%esi
 4a4bcf9:	48 89 55 b8          	mov    %rdx,-0x48(%rbp)
 4a4bcfd:	e8 3e 1f fd ff       	call   4a1dc40 <__gmpz_realloc>
 4a4bd02:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
 4a4bd06:	48 89 c3             	mov    %rax,%rbx
 4a4bd09:	e9 fb fd ff ff       	jmp    4a4bb09 <__gmpz_gcd+0x379>
 4a4bd0e:	e8 dd 91 0b 00       	call   4b04ef0 <__stack_chk_fail@plt>

Disassembly of section .init:

Disassembly of section .fini:

Disassembly of section .plt:
