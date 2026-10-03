
/home/kim/worktrees/hex-dev/hex-dev-issue-10377-allocation/.lake/build/bin/hexsigndet_bench:     file format elf64-x86-64


Disassembly of section .text:

0000000004a4bd50 <__gmpn_gcd>:
 4a4bd50:	55                   	push   %rbp
 4a4bd51:	49 89 d2             	mov    %rdx,%r10
 4a4bd54:	48 89 e5             	mov    %rsp,%rbp
 4a4bd57:	41 57                	push   %r15
 4a4bd59:	41 56                	push   %r14
 4a4bd5b:	41 55                	push   %r13
 4a4bd5d:	41 54                	push   %r12
 4a4bd5f:	49 89 d4             	mov    %rdx,%r12
 4a4bd62:	53                   	push   %rbx
 4a4bd63:	4d 29 c4             	sub    %r8,%r12
 4a4bd66:	49 89 f5             	mov    %rsi,%r13
 4a4bd69:	49 83 c4 01          	add    $0x1,%r12
 4a4bd6d:	49 89 ce             	mov    %rcx,%r14
 4a4bd70:	4c 89 c3             	mov    %r8,%rbx
 4a4bd73:	48 81 ec 98 00 00 00 	sub    $0x98,%rsp
 4a4bd7a:	48 89 bd 48 ff ff ff 	mov    %rdi,-0xb8(%rbp)
 4a4bd81:	64 48 8b 04 25 28 00 	mov    %fs:0x28,%rax
 4a4bd88:	00 00 
 4a4bd8a:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
 4a4bd8e:	31 c0                	xor    %eax,%eax
 4a4bd90:	4d 39 c4             	cmp    %r8,%r12
 4a4bd93:	4d 0f 4c e0          	cmovl  %r8,%r12
 4a4bd97:	49 81 f8 e7 03 00 00 	cmp    $0x3e7,%r8
 4a4bd9e:	7e 6d                	jle    4a4be0d <__gmpn_gcd+0xbd>
 4a4bda0:	48 89 95 60 ff ff ff 	mov    %rdx,-0xa0(%rbp)
 4a4bda7:	4b 8d 14 00          	lea    (%r8,%r8,1),%rdx
 4a4bdab:	49 bf ab aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%r15
 4a4bdb2:	aa aa aa 
 4a4bdb5:	4c 89 c1             	mov    %r8,%rcx
 4a4bdb8:	48 89 d0             	mov    %rdx,%rax
 4a4bdbb:	49 f7 e7             	mul    %r15
 4a4bdbe:	48 d1 ea             	shr    $1,%rdx
 4a4bdc1:	48 29 d1             	sub    %rdx,%rcx
 4a4bdc4:	49 89 d7             	mov    %rdx,%r15
 4a4bdc7:	48 89 cf             	mov    %rcx,%rdi
 4a4bdca:	48 89 8d 68 ff ff ff 	mov    %rcx,-0x98(%rbp)
 4a4bdd1:	e8 4a a2 ff ff       	call   4a46020 <__gmpn_hgcd_itch>
 4a4bdd6:	48 8b 8d 68 ff ff ff 	mov    -0x98(%rbp),%rcx
 4a4bddd:	4c 8b 95 60 ff ff ff 	mov    -0xa0(%rbp),%r10
 4a4bde4:	48 83 c1 01          	add    $0x1,%rcx
 4a4bde8:	48 89 ca             	mov    %rcx,%rdx
 4a4bdeb:	48 c1 ea 3f          	shr    $0x3f,%rdx
 4a4bdef:	48 01 ca             	add    %rcx,%rdx
 4a4bdf2:	49 8d 4c 1f ff       	lea    -0x1(%r15,%rbx,1),%rcx
 4a4bdf7:	48 d1 fa             	sar    $1,%rdx
 4a4bdfa:	48 39 c1             	cmp    %rax,%rcx
 4a4bdfd:	48 0f 4c c8          	cmovl  %rax,%rcx
 4a4be01:	48 8d 44 91 04       	lea    0x4(%rcx,%rdx,4),%rax
 4a4be06:	49 39 c4             	cmp    %rax,%r12
 4a4be09:	4c 0f 4c e0          	cmovl  %rax,%r12
 4a4be0d:	4a 8d 34 e5 00 00 00 	lea    0x0(,%r12,8),%rsi
 4a4be14:	00 
 4a4be15:	48 c7 85 78 ff ff ff 	movq   $0x0,-0x88(%rbp)
 4a4be1c:	00 00 00 00 
 4a4be20:	48 81 fe 00 7f 00 00 	cmp    $0x7f00,%rsi
 4a4be27:	0f 87 83 03 00 00    	ja     4a4c1b0 <__gmpn_gcd+0x460>
 4a4be2d:	48 83 c6 1e          	add    $0x1e,%rsi
 4a4be31:	48 83 e6 f0          	and    $0xfffffffffffffff0,%rsi
 4a4be35:	48 29 f4             	sub    %rsi,%rsp
 4a4be38:	4c 8d 7c 24 0f       	lea    0xf(%rsp),%r15
 4a4be3d:	49 83 e7 f0          	and    $0xfffffffffffffff0,%r15
 4a4be41:	4c 39 d3             	cmp    %r10,%rbx
 4a4be44:	0f 8c e6 02 00 00    	jl     4a4c130 <__gmpn_gcd+0x3e0>
 4a4be4a:	48 8b 85 48 ff ff ff 	mov    -0xb8(%rbp),%rax
 4a4be51:	48 81 fb e7 03 00 00 	cmp    $0x3e7,%rbx
 4a4be58:	48 89 45 80          	mov    %rax,-0x80(%rbp)
 4a4be5c:	0f 8e 58 01 00 00    	jle    4a4bfba <__gmpn_gcd+0x26a>
 4a4be62:	48 8d 45 90          	lea    -0x70(%rbp),%rax
 4a4be66:	4c 89 ad 60 ff ff ff 	mov    %r13,-0xa0(%rbp)
 4a4be6d:	49 89 dd             	mov    %rbx,%r13
 4a4be70:	48 89 85 68 ff ff ff 	mov    %rax,-0x98(%rbp)
 4a4be77:	48 8d 45 80          	lea    -0x80(%rbp),%rax
 4a4be7b:	48 89 85 50 ff ff ff 	mov    %rax,-0xb0(%rbp)
 4a4be82:	eb 38                	jmp    4a4bebc <__gmpn_gcd+0x16c>
 4a4be84:	0f 1f 40 00          	nopl   0x0(%rax)
 4a4be88:	4c 8b 8d 58 ff ff ff 	mov    -0xa8(%rbp),%r9
 4a4be8f:	48 8b 95 60 ff ff ff 	mov    -0xa0(%rbp),%rdx
 4a4be96:	49 8d 34 04          	lea    (%r12,%rax,1),%rsi
 4a4be9a:	48 8b bd 68 ff ff ff 	mov    -0x98(%rbp),%rdi
 4a4bea1:	4d 89 e0             	mov    %r12,%r8
 4a4bea4:	4c 89 f1             	mov    %r14,%rcx
 4a4bea7:	e8 e4 b8 ff ff       	call   4a47790 <__gmpn_hgcd_matrix_adjust>
 4a4beac:	49 89 c5             	mov    %rax,%r13
 4a4beaf:	49 81 fd e7 03 00 00 	cmp    $0x3e7,%r13
 4a4beb6:	0f 8e f4 00 00 00    	jle    4a4bfb0 <__gmpn_gcd+0x260>
 4a4bebc:	4b 8d 54 2d 00       	lea    0x0(%r13,%r13,1),%rdx
 4a4bec1:	48 b8 ab aa aa aa aa 	movabs $0xaaaaaaaaaaaaaaab,%rax
 4a4bec8:	aa aa aa 
 4a4becb:	48 8b bd 68 ff ff ff 	mov    -0x98(%rbp),%rdi
 4a4bed2:	4c 89 eb             	mov    %r13,%rbx
 4a4bed5:	48 f7 e2             	mul    %rdx
 4a4bed8:	48 d1 ea             	shr    $1,%rdx
 4a4bedb:	48 29 d3             	sub    %rdx,%rbx
 4a4bede:	49 89 d4             	mov    %rdx,%r12
 4a4bee1:	4c 89 fa             	mov    %r15,%rdx
 4a4bee4:	48 89 de             	mov    %rbx,%rsi
 4a4bee7:	e8 f4 b3 ff ff       	call   4a472e0 <__gmpn_hgcd_matrix_init>
 4a4beec:	48 8d 53 01          	lea    0x1(%rbx),%rdx
 4a4bef0:	4a 8d 3c e5 00 00 00 	lea    0x0(,%r12,8),%rdi
 4a4bef7:	00 
 4a4bef8:	48 8b 8d 68 ff ff ff 	mov    -0x98(%rbp),%rcx
 4a4beff:	49 89 d1             	mov    %rdx,%r9
 4a4bf02:	49 8d 34 3e          	lea    (%r14,%rdi,1),%rsi
 4a4bf06:	48 03 bd 60 ff ff ff 	add    -0xa0(%rbp),%rdi
 4a4bf0d:	49 c1 e9 3f          	shr    $0x3f,%r9
 4a4bf11:	49 01 d1             	add    %rdx,%r9
 4a4bf14:	48 89 da             	mov    %rbx,%rdx
 4a4bf17:	49 d1 f9             	sar    $1,%r9
 4a4bf1a:	49 83 c1 01          	add    $0x1,%r9
 4a4bf1e:	49 c1 e1 05          	shl    $0x5,%r9
 4a4bf22:	4d 01 f9             	add    %r15,%r9
 4a4bf25:	4d 89 c8             	mov    %r9,%r8
 4a4bf28:	4c 89 8d 58 ff ff ff 	mov    %r9,-0xa8(%rbp)
 4a4bf2f:	e8 4c a1 ff ff       	call   4a46080 <__gmpn_hgcd>
 4a4bf34:	48 85 c0             	test   %rax,%rax
 4a4bf37:	0f 8f 4b ff ff ff    	jg     4a4be88 <__gmpn_gcd+0x138>
 4a4bf3d:	48 83 ec 08          	sub    $0x8,%rsp
 4a4bf41:	4c 8b 8d 50 ff ff ff 	mov    -0xb0(%rbp),%r9
 4a4bf48:	48 8b bd 60 ff ff ff 	mov    -0xa0(%rbp),%rdi
 4a4bf4f:	41 57                	push   %r15
 4a4bf51:	4c 8d 05 c8 fd ff ff 	lea    -0x238(%rip),%r8        # 4a4bd20 <gcd_hook>
 4a4bf58:	31 c9                	xor    %ecx,%ecx
 4a4bf5a:	4c 89 ea             	mov    %r13,%rdx
 4a4bf5d:	4c 89 f6             	mov    %r14,%rsi
 4a4bf60:	e8 5b cc ff ff       	call   4a48bc0 <__gmpn_gcd_subdiv_step>
 4a4bf65:	48 85 c0             	test   %rax,%rax
 4a4bf68:	49 89 c5             	mov    %rax,%r13
 4a4bf6b:	59                   	pop    %rcx
 4a4bf6c:	5e                   	pop    %rsi
 4a4bf6d:	0f 85 3c ff ff ff    	jne    4a4beaf <__gmpn_gcd+0x15f>
 4a4bf73:	48 8b bd 78 ff ff ff 	mov    -0x88(%rbp),%rdi
 4a4bf7a:	48 85 ff             	test   %rdi,%rdi
 4a4bf7d:	0f 85 9e 01 00 00    	jne    4a4c121 <__gmpn_gcd+0x3d1>
 4a4bf83:	48 8b 5d c8          	mov    -0x38(%rbp),%rbx
 4a4bf87:	64 48 33 1c 25 28 00 	xor    %fs:0x28,%rbx
 4a4bf8e:	00 00 
 4a4bf90:	48 8b 45 88          	mov    -0x78(%rbp),%rax
 4a4bf94:	0f 85 a7 02 00 00    	jne    4a4c241 <__gmpn_gcd+0x4f1>
 4a4bf9a:	48 8d 65 d8          	lea    -0x28(%rbp),%rsp
 4a4bf9e:	5b                   	pop    %rbx
 4a4bf9f:	41 5c                	pop    %r12
 4a4bfa1:	41 5d                	pop    %r13
 4a4bfa3:	41 5e                	pop    %r14
 4a4bfa5:	41 5f                	pop    %r15
 4a4bfa7:	5d                   	pop    %rbp
 4a4bfa8:	c3                   	ret
 4a4bfa9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
 4a4bfb0:	4c 89 eb             	mov    %r13,%rbx
 4a4bfb3:	4c 8b ad 60 ff ff ff 	mov    -0xa0(%rbp),%r13
 4a4bfba:	48 83 fb 02          	cmp    $0x2,%rbx
 4a4bfbe:	0f 8e 0f 01 00 00    	jle    4a4c0d3 <__gmpn_gcd+0x383>
 4a4bfc4:	4c 8d 65 80          	lea    -0x80(%rbp),%r12
 4a4bfc8:	48 8d 45 90          	lea    -0x70(%rbp),%rax
 4a4bfcc:	4c 89 a5 68 ff ff ff 	mov    %r12,-0x98(%rbp)
 4a4bfd3:	49 89 c4             	mov    %rax,%r12
 4a4bfd6:	eb 32                	jmp    4a4c00a <__gmpn_gcd+0x2ba>
 4a4bfd8:	0f 1f 84 00 00 00 00 	nopl   0x0(%rax,%rax,1)
 4a4bfdf:	00 
 4a4bfe0:	49 89 d8             	mov    %rbx,%r8
 4a4bfe3:	4c 89 ea             	mov    %r13,%rdx
 4a4bfe6:	4c 89 fe             	mov    %r15,%rsi
 4a4bfe9:	4c 89 f1             	mov    %r14,%rcx
 4a4bfec:	4c 89 e7             	mov    %r12,%rdi
 4a4bfef:	e8 bc d1 ff ff       	call   4a491b0 <__gmpn_matrix22_mul1_inverse_vector>
 4a4bff4:	48 89 c3             	mov    %rax,%rbx
 4a4bff7:	4c 89 e8             	mov    %r13,%rax
 4a4bffa:	4d 89 fd             	mov    %r15,%r13
 4a4bffd:	48 83 fb 02          	cmp    $0x2,%rbx
 4a4c001:	49 89 c7             	mov    %rax,%r15
 4a4c004:	0f 8e c9 00 00 00    	jle    4a4c0d3 <__gmpn_gcd+0x383>
 4a4c00a:	4c 8d 04 dd 00 00 00 	lea    0x0(,%rbx,8),%r8
 4a4c011:	00 
 4a4c012:	4b 8b 7c 05 f8       	mov    -0x8(%r13,%r8,1),%rdi
 4a4c017:	4b 8b 54 06 f8       	mov    -0x8(%r14,%r8,1),%rdx
 4a4c01c:	4b 8b 74 05 f0       	mov    -0x10(%r13,%r8,1),%rsi
 4a4c021:	4f 8b 4c 06 f0       	mov    -0x10(%r14,%r8,1),%r9
 4a4c026:	48 89 f8             	mov    %rdi,%rax
 4a4c029:	48 09 d0             	or     %rdx,%rax
 4a4c02c:	78 56                	js     4a4c084 <__gmpn_gcd+0x334>
 4a4c02e:	48 0f bd c0          	bsr    %rax,%rax
 4a4c032:	41 ba 40 00 00 00    	mov    $0x40,%r10d
 4a4c038:	83 f0 3f             	xor    $0x3f,%eax
 4a4c03b:	49 89 f3             	mov    %rsi,%r11
 4a4c03e:	41 29 c2             	sub    %eax,%r10d
 4a4c041:	89 c1                	mov    %eax,%ecx
 4a4c043:	48 d3 e7             	shl    %cl,%rdi
 4a4c046:	44 89 d1             	mov    %r10d,%ecx
 4a4c049:	49 d3 eb             	shr    %cl,%r11
 4a4c04c:	44 89 d1             	mov    %r10d,%ecx
 4a4c04f:	4c 09 df             	or     %r11,%rdi
 4a4c052:	4f 8b 5c 05 e8       	mov    -0x18(%r13,%r8,1),%r11
 4a4c057:	4f 8b 44 06 e8       	mov    -0x18(%r14,%r8,1),%r8
 4a4c05c:	49 d3 eb             	shr    %cl,%r11
 4a4c05f:	89 c1                	mov    %eax,%ecx
 4a4c061:	48 d3 e6             	shl    %cl,%rsi
 4a4c064:	48 d3 e2             	shl    %cl,%rdx
 4a4c067:	44 89 d1             	mov    %r10d,%ecx
 4a4c06a:	4c 09 de             	or     %r11,%rsi
 4a4c06d:	4d 89 cb             	mov    %r9,%r11
 4a4c070:	49 d3 eb             	shr    %cl,%r11
 4a4c073:	44 89 d1             	mov    %r10d,%ecx
 4a4c076:	49 d3 e8             	shr    %cl,%r8
 4a4c079:	89 c1                	mov    %eax,%ecx
 4a4c07b:	4c 09 da             	or     %r11,%rdx
 4a4c07e:	49 d3 e1             	shl    %cl,%r9
 4a4c081:	4d 09 c1             	or     %r8,%r9
 4a4c084:	4d 89 e0             	mov    %r12,%r8
 4a4c087:	4c 89 c9             	mov    %r9,%rcx
 4a4c08a:	e8 21 bc ff ff       	call   4a47cb0 <__gmpn_hgcd2>
 4a4c08f:	85 c0                	test   %eax,%eax
 4a4c091:	0f 85 49 ff ff ff    	jne    4a4bfe0 <__gmpn_gcd+0x290>
 4a4c097:	48 83 ec 08          	sub    $0x8,%rsp
 4a4c09b:	4c 8b 8d 68 ff ff ff 	mov    -0x98(%rbp),%r9
 4a4c0a2:	4c 8d 05 77 fc ff ff 	lea    -0x389(%rip),%r8        # 4a4bd20 <gcd_hook>
 4a4c0a9:	41 57                	push   %r15
 4a4c0ab:	48 89 da             	mov    %rbx,%rdx
 4a4c0ae:	31 c9                	xor    %ecx,%ecx
 4a4c0b0:	4c 89 f6             	mov    %r14,%rsi
 4a4c0b3:	4c 89 ef             	mov    %r13,%rdi
 4a4c0b6:	e8 05 cb ff ff       	call   4a48bc0 <__gmpn_gcd_subdiv_step>
 4a4c0bb:	48 89 c3             	mov    %rax,%rbx
 4a4c0be:	48 85 db             	test   %rbx,%rbx
 4a4c0c1:	58                   	pop    %rax
 4a4c0c2:	5a                   	pop    %rdx
 4a4c0c3:	0f 84 aa fe ff ff    	je     4a4bf73 <__gmpn_gcd+0x223>
 4a4c0c9:	48 83 fb 02          	cmp    $0x2,%rbx
 4a4c0cd:	0f 8f 37 ff ff ff    	jg     4a4c00a <__gmpn_gcd+0x2ba>
 4a4c0d3:	49 8b 7d 00          	mov    0x0(%r13),%rdi
 4a4c0d7:	49 8b 36             	mov    (%r14),%rsi
 4a4c0da:	40 f6 c7 01          	test   $0x1,%dil
 4a4c0de:	0f 84 ac 00 00 00    	je     4a4c190 <__gmpn_gcd+0x440>
 4a4c0e4:	48 83 fb 01          	cmp    $0x1,%rbx
 4a4c0e8:	0f 85 ea 00 00 00    	jne    4a4c1d8 <__gmpn_gcd+0x488>
 4a4c0ee:	48 8d 05 cb 83 2d 00 	lea    0x2d83cb(%rip),%rax        # 4d244c0 <__gmpn_cpuvec>
 4a4c0f5:	48 0f bc ce          	bsf    %rsi,%rcx
 4a4c0f9:	48 d3 ee             	shr    %cl,%rsi
 4a4c0fc:	ff 50 68             	call   *0x68(%rax)
 4a4c0ff:	48 8b bd 78 ff ff ff 	mov    -0x88(%rbp),%rdi
 4a4c106:	48 8b 9d 48 ff ff ff 	mov    -0xb8(%rbp),%rbx
 4a4c10d:	48 c7 45 88 01 00 00 	movq   $0x1,-0x78(%rbp)
 4a4c114:	00 
 4a4c115:	48 85 ff             	test   %rdi,%rdi
 4a4c118:	48 89 03             	mov    %rax,(%rbx)
 4a4c11b:	0f 84 62 fe ff ff    	je     4a4bf83 <__gmpn_gcd+0x233>
 4a4c121:	e8 3a 36 fd ff       	call   4a1f760 <__gmp_tmp_reentrant_free>
 4a4c126:	e9 58 fe ff ff       	jmp    4a4bf83 <__gmpn_gcd+0x233>
 4a4c12b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
 4a4c130:	48 83 ec 08          	sub    $0x8,%rsp
 4a4c134:	4d 89 d0             	mov    %r10,%r8
 4a4c137:	4c 89 ff             	mov    %r15,%rdi
 4a4c13a:	53                   	push   %rbx
 4a4c13b:	4d 89 f1             	mov    %r14,%r9
 4a4c13e:	4c 89 e9             	mov    %r13,%rcx
 4a4c141:	31 d2                	xor    %edx,%edx
 4a4c143:	4c 89 ee             	mov    %r13,%rsi
 4a4c146:	e8 85 c0 fe ff       	call   4a381d0 <__gmpn_tdiv_qr>
 4a4c14b:	5f                   	pop    %rdi
 4a4c14c:	41 58                	pop    %r8
 4a4c14e:	48 89 d8             	mov    %rbx,%rax
 4a4c151:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
 4a4c158:	48 83 e8 01          	sub    $0x1,%rax
 4a4c15c:	49 83 7c c5 00 00    	cmpq   $0x0,0x0(%r13,%rax,8)
 4a4c162:	0f 85 e2 fc ff ff    	jne    4a4be4a <__gmpn_gcd+0xfa>
 4a4c168:	48 85 c0             	test   %rax,%rax
 4a4c16b:	75 eb                	jne    4a4c158 <__gmpn_gcd+0x408>
 4a4c16d:	48 8d 05 4c 83 2d 00 	lea    0x2d834c(%rip),%rax        # 4d244c0 <__gmpn_cpuvec>
 4a4c174:	48 89 da             	mov    %rbx,%rdx
 4a4c177:	4c 89 f6             	mov    %r14,%rsi
 4a4c17a:	48 8b bd 48 ff ff ff 	mov    -0xb8(%rbp),%rdi
 4a4c181:	ff 50 50             	call   *0x50(%rax)
 4a4c184:	48 89 5d 88          	mov    %rbx,-0x78(%rbp)
 4a4c188:	e9 e6 fd ff ff       	jmp    4a4bf73 <__gmpn_gcd+0x223>
 4a4c18d:	0f 1f 00             	nopl   (%rax)
 4a4c190:	48 89 f8             	mov    %rdi,%rax
 4a4c193:	48 89 f7             	mov    %rsi,%rdi
 4a4c196:	48 89 c6             	mov    %rax,%rsi
 4a4c199:	4c 89 e8             	mov    %r13,%rax
 4a4c19c:	4d 89 f5             	mov    %r14,%r13
 4a4c19f:	49 89 c6             	mov    %rax,%r14
 4a4c1a2:	e9 3d ff ff ff       	jmp    4a4c0e4 <__gmpn_gcd+0x394>
 4a4c1a7:	66 0f 1f 84 00 00 00 	nopw   0x0(%rax,%rax,1)
 4a4c1ae:	00 00 
 4a4c1b0:	48 8d bd 78 ff ff ff 	lea    -0x88(%rbp),%rdi
 4a4c1b7:	4c 89 95 68 ff ff ff 	mov    %r10,-0x98(%rbp)
 4a4c1be:	e8 5d 35 fd ff       	call   4a1f720 <__gmp_tmp_reentrant_alloc>
 4a4c1c3:	4c 8b 95 68 ff ff ff 	mov    -0x98(%rbp),%r10
 4a4c1ca:	49 89 c7             	mov    %rax,%r15
 4a4c1cd:	e9 6f fc ff ff       	jmp    4a4be41 <__gmpn_gcd+0xf1>
 4a4c1d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
 4a4c1d8:	48 85 f6             	test   %rsi,%rsi
 4a4c1db:	49 8b 56 08          	mov    0x8(%r14),%rdx
 4a4c1df:	74 59                	je     4a4c23a <__gmpn_gcd+0x4ea>
 4a4c1e1:	40 f6 c6 01          	test   $0x1,%sil
 4a4c1e5:	75 1e                	jne    4a4c205 <__gmpn_gcd+0x4b5>
 4a4c1e7:	48 0f bc c6          	bsf    %rsi,%rax
 4a4c1eb:	89 c1                	mov    %eax,%ecx
 4a4c1ed:	48 89 d3             	mov    %rdx,%rbx
 4a4c1f0:	48 d3 ee             	shr    %cl,%rsi
 4a4c1f3:	b9 40 00 00 00       	mov    $0x40,%ecx
 4a4c1f8:	29 c1                	sub    %eax,%ecx
 4a4c1fa:	48 d3 e3             	shl    %cl,%rbx
 4a4c1fd:	89 c1                	mov    %eax,%ecx
 4a4c1ff:	48 09 de             	or     %rbx,%rsi
 4a4c202:	48 d3 ea             	shr    %cl,%rdx
 4a4c205:	49 8b 45 08          	mov    0x8(%r13),%rax
 4a4c209:	48 89 f1             	mov    %rsi,%rcx
 4a4c20c:	48 89 fe             	mov    %rdi,%rsi
 4a4c20f:	48 89 c7             	mov    %rax,%rdi
 4a4c212:	e8 69 00 00 00       	call   4a4c280 <__gmpn_gcd_22>
 4a4c217:	48 8b 9d 48 ff ff ff 	mov    -0xb8(%rbp),%rbx
 4a4c21e:	48 89 03             	mov    %rax,(%rbx)
 4a4c221:	31 c0                	xor    %eax,%eax
 4a4c223:	48 85 d2             	test   %rdx,%rdx
 4a4c226:	0f 95 c0             	setne  %al
 4a4c229:	48 89 53 08          	mov    %rdx,0x8(%rbx)
 4a4c22d:	48 83 c0 01          	add    $0x1,%rax
 4a4c231:	48 89 45 88          	mov    %rax,-0x78(%rbp)
 4a4c235:	e9 39 fd ff ff       	jmp    4a4bf73 <__gmpn_gcd+0x223>
 4a4c23a:	48 89 d6             	mov    %rdx,%rsi
 4a4c23d:	31 d2                	xor    %edx,%edx
 4a4c23f:	eb a0                	jmp    4a4c1e1 <__gmpn_gcd+0x491>
 4a4c241:	e8 aa 8c 0b 00       	call   4b04ef0 <__stack_chk_fail@plt>

Disassembly of section .init:

Disassembly of section .fini:

Disassembly of section .plt:
