movl X4 , %eax ; leal 0 ( , %eax , 8 ) , %edx ; movl X1 , %eax ; addl %edx , %eax ; movl %eax , X3 ; movl X3 , %edx ; movl X1 , %eax ; cmpl %eax , %edx ; jge .L0 ; movl X2 , %eax ; addl 1 , %eax ; movl %eax , X2 ; .L0 : ; movl X4 , %eax ; sarl 29 , %eax ; movl %eax , %edx ; movl X2 , %eax ; addl %edx , %eax ; movl %eax , X2 ; movl X3 , %eax ; movl %eax , X1 ;
movl X2 , %eax ; leal 63 ( %eax ) , %edx ; testl %eax , %eax ; cmovs %edx , %eax ; sarl 6 , %eax ; movl %eax , X1 ; movl X1 , %eax ; testl %eax , %eax ; jle .L0 ; movl X1 , %eax ; sall 6 , %eax ; movl %eax , X1 ; movl X1 , %eax ; movl %eax , X3 ; movl X3 , %eax ; movl %eax , X3 ; movl X2 , %edx ; movl X1 , %eax ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X2 ; .L0 : ; movl X2 , %eax ; testl %eax , %eax ; je .L1 ; movl X4 , %eax ; movl %eax , X6 ; movl X2 , %eax ; movl %eax , X5 ; .L1 : ;
movl X1 , %eax ; cmpl 63 , %eax ; jg .L0 ; movl X1 , %edx ; movl X4 , %eax ; addl %edx , %eax ; cmpl 63 , %eax ; jle .L1 ; .L0 : ; movl X4 , %eax ; movl 64 , %edx ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X4 ; movl X3 , %edx ; movl X4 , %eax ; addl %edx , %eax ; movl %eax , X3 ; movl X1 , %edx ; movl X4 , %eax ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X1 ; movl 0 , X2 ; jmp .L2 ; .L1 : ; movl X2 , %edx ; movl X1 , %eax ; addl %edx , %eax ; movl %eax , X2 ; .L2 : ;
movl X1 , %eax ; testl %eax , %eax ; je .L1 ; movl X1 , %edx ; movl X2 , %eax ; addl %eax , %edx ; movl X4 , %eax ; cmpl %eax , %edx ; jl .L0 ; movl X4 , %edx ; movl X1 , %eax ; subl %eax , %edx ; movl X3 , %eax ; addl %edx , %eax ; movl %eax , X3 ; movl X2 , %eax ; movl X4 , %ecx ; movl X1 , %edx ; subl %edx , %ecx ; movl %ecx , %edx ; subl %edx , %eax ; movl %eax , X2 ; movl 0 , X1 ; jmp .L1 ; .L0 : ; movl X1 , %edx ; movl X2 , %eax ; addl %edx , %eax ; movl %eax , X1 ; .L1 : ;
movl X2 , %eax ; movl %eax , X1 ; jmp .L1 ; .L0 : ; movl X5 , %edx ; movl X3 , %eax ; addl %edx , %eax ; movl %eax , X5 ; movl X4 , %edx ; movl X3 , %eax ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X4 ; .L1 : ; movl X4 , %edx ; movl X3 , %eax ; cmpl %eax , %edx ; jge .L0 ; movl X4 , %eax ; movl %eax , X6 ;
movl X3 , %eax ; movl %eax , X1 ; movl 0 , X2 ; jmp .L1 ; .L0 : ; movl X8 , %eax ; movl %eax , X4 ; movl X9 , %eax ; movl %eax , X7 ; movl X7 , %eax ; movl %eax , X5 ; movl X7 , %edx ; movl X10 , %eax ; xorl %edx , %eax ; movl %eax , X6 ; movl X2 , %eax ; addl 1 , %eax ; movl %eax , X2 ; .L1 : ; movl X2 , %eax ; cmpl 15 , %eax ; jle .L0 ;
movl 0 , X1 ; jmp .L3 ; .L0 : ; movl 0 , X3 ; jmp .L2 ; .L1 : ; movl X4 , %edx ; movl X5 , %eax ; xorl %edx , %eax ; movl %eax , X4 ; movl X4 , %eax ; movl %eax , X1 ; movl X3 , %eax ; addl 8 , %eax ; movl %eax , X3 ; .L2 : ; movl X3 , %eax ; cmpl 47 , %eax ; jle .L1 ; movl X1 , %edx ; movl X2 , %eax ; addl %edx , %eax ; movzbl %al , %eax ; movl %eax , X1 ; movl X2 , %eax ; addl 1 , %eax ; movl %eax , X2 ; .L3 : ; movl X2 , %eax ; cmpl 17 , %eax ; jle .L0 ;
movl X2 , %eax ; movl %eax , X1 ; movl X4 , %eax ; movl %eax , X3 ; movl X6 , %eax ; sarl 3 , %eax ; movl %eax , X5 ; movl X5 , %eax ; testl %eax , %eax ; je .L2 ; jmp .L1 ; .L0 : ; movl X1 , %eax ; addl 1 , %eax ; movzbl %al , %eax ; movl %eax , X1 ; movl X7 , %eax ; movl %eax , X6 ; movl X6 , %edx ; movl X3 , %eax ; addl %edx , %eax ; movzbl %al , %eax ; movl %eax , X3 ; movl X8 , %eax ; movl %eax , X7 ; movl X6 , %eax ; movl %eax , X8 ; .L1 : ; movl X5 , %eax ; subl 1 , %eax ; movl %eax , X5 ; movl X5 , %eax ; testl %eax , %eax ; jg .L0 ; .L2 : ;
movl X2 , %eax ; movl %eax , X1 ; movl X1 , %eax ; movzwl %ax , %eax ; movl %eax , X3 ; movl X1 , %eax ; sarl 16 , %eax ; movl %eax , X4 ;
movl X1 , %eax ; subl 1 , %eax ; movl %eax , X1 ; movl X1 , %eax ; testl %eax , %eax ; jne .L2 ; movl X2 , %eax ; cmpl 2 , %eax ; jne .L0 ; movl 6 , X1 ; jmp .L1 ; .L0 : ; movl 5 , X1 ; .L1 : ; movl X4 , %eax ; andl 63 , %eax ; movl %eax , %edx ; movl X3 , %eax ; addl %edx , %eax ; movl %eax , X3 ; movl X3 , %eax ; andl 63 , %eax ; movl %eax , %edx ; movl X5 , %eax ; addl %edx , %eax ; movl %eax , X5 ; movl X5 , %eax ; andl 63 , %eax ; movl %eax , %edx ; movl X6 , %eax ; addl %edx , %eax ; movl %eax , X6 ; movl X6 , %eax ; andl 63 , %eax ; movl %eax , %edx ; movl X4 , %eax ; addl %edx , %eax ; movl %eax , X4 ; .L2 : ; movl X3 , %eax ; movzwl %ax , %eax ; movl X5 , %edx ; sall 16 , %edx ; orl %edx , %eax ; movl %eax , X7 ; movl X6 , %eax ; movzwl %ax , %eax ; movl X4 , %edx ; sall 16 , %edx ; orl %edx , %eax ; movl %eax , X8 ;
movl X4 , %eax ; leal 0 ( , %eax , 8 ) , %edx ; movl X2 , %eax ; addl %edx , %eax ; movl %eax , X1 ; movl X1 , %edx ; movl X2 , %eax ; cmpl %eax , %edx ; jge .L0 ; movl X3 , %eax ; addl 1 , %eax ; movl %eax , X3 ; .L0 : ; movl X4 , %eax ; sarl 29 , %eax ; movl %eax , %edx ; movl X3 , %eax ; addl %edx , %eax ; movl %eax , X3 ; movl X1 , %eax ; movl %eax , X2 ;
movl X2 , %eax ; leal 63 ( %eax ) , %edx ; testl %eax , %eax ; cmovs %edx , %eax ; sarl 6 , %eax ; movl %eax , X1 ; movl X1 , %eax ; testl %eax , %eax ; jle .L0 ; movl X1 , %eax ; sall 6 , %eax ; movl %eax , X1 ; movl X3 , %edx ; movl X1 , %eax ; addl %edx , %eax ; movl %eax , X3 ; movl X2 , %edx ; movl X1 , %eax ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X2 ; .L0 : ; movl X2 , %eax ; testl %eax , %eax ; je .L1 ; movl X5 , %eax ; movl %eax , X4 ; movl X2 , %eax ; movl %eax , X6 ; .L1 : ;
movl X2 , %eax ; movl %eax , X1 ; movl X1 , %eax ; testl %eax , %eax ; je .L2 ; movl X3 , %eax ; cmpl 63 , %eax ; jg .L0 ; movl X3 , %edx ; movl X1 , %eax ; addl %edx , %eax ; cmpl 63 , %eax ; jle .L1 ; .L0 : ; movl X1 , %eax ; movl 64 , %edx ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X1 ; movl X4 , %edx ; movl X1 , %eax ; addl %edx , %eax ; movl %eax , X4 ; movl X3 , %edx ; movl X1 , %eax ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X3 ; movl 0 , X2 ; jmp .L2 ; .L1 : ; movl X2 , %edx ; movl X3 , %eax ; addl %edx , %eax ; movl %eax , X2 ; .L2 : ;
movl X2 , %eax ; movl 56 , %edx ; movl %edx , %ecx ; sarl %cl , %eax ; movl %eax , X1 ; movl X2 , %eax ; movl 48 , %edx ; movl %edx , %ecx ; sarl %cl , %eax ; movl %eax , X3 ; movl X2 , %eax ; movl 40 , %edx ; movl %edx , %ecx ; sarl %cl , %eax ; movl %eax , X4 ; movl X2 , %eax ; movl 32 , %edx ; movl %edx , %ecx ; sarl %cl , %eax ; movl %eax , X5 ; movl X2 , %eax ; sarl 24 , %eax ; movl %eax , X6 ;
movl X1 , %eax ; cmpl 48 , %eax ; jne .L2 ; movl 0 , X2 ; jmp .L1 ; .L0 : ; movl X4 , %eax ; movl %eax , X3 ; movl X3 , %eax ; sarl 16 , %eax ; movl %eax , X6 ; movl X3 , %eax ; movl %eax , X7 ; movl X2 , %eax ; addl 1 , %eax ; movl %eax , X2 ; .L1 : ; movl X2 , %eax ; cmpl 5 , %eax ; jle .L0 ; .L2 : ; movl X1 , %eax ; cmpl 64 , %eax ; jne .L5 ; movl 0 , X2 ; jmp .L4 ; .L3 : ; movl X4 , %eax ; movl %eax , X3 ; movl X3 , %eax ; sarl 24 , %eax ; movl %eax , X6 ; movl X3 , %eax ; sarl 8 , %eax ; movl %eax , X7 ; movl X2 , %eax ; addl 1 , %eax ; movl %eax , X2 ; .L4 : ; movl X2 , %eax ; cmpl 7 , %eax ; jle .L3 ; .L5 : ;
movl X3 , %eax ; leal 0 ( , %eax , 8 ) , %edx ; movl X2 , %eax ; addl %edx , %eax ; movl %eax , X1 ; movl X1 , %edx ; movl X2 , %eax ; cmpl %eax , %edx ; jge .L0 ; movl X4 , %eax ; addl 1 , %eax ; movl %eax , X4 ; .L0 : ; movl X5 , %eax ; cmpl 7 , %eax ; jle .L1 ; movl X3 , %eax ; movl 61 , %edx ; movl %edx , %ecx ; sarl %cl , %eax ; movl %eax , %edx ; movl X4 , %eax ; addl %edx , %eax ; movl %eax , X4 ; .L1 : ; movl X1 , %eax ; movl %eax , X2 ;
movl X1 , %eax ; testl %eax , %eax ; je .L0 ; movl X3 , %edx ; movl X1 , %eax ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X2 ; movl X4 , %edx ; movl X2 , %eax ; cmpl %eax , %edx ; jl .L0 ; movl X4 , %edx ; movl X2 , %eax ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X4 ; movl X5 , %edx ; movl X2 , %eax ; addl %edx , %eax ; movl %eax , X5 ; .L0 : ;
movl X2 , %eax ; movl %eax , X1 ; movl X1 , %eax ; testl %eax , %eax ; je .L1 ; movl X4 , %edx ; movl X1 , %eax ; subl %eax , %edx ; movl X3 , %eax ; cmpl %eax , %edx ; jle .L0 ; movl X2 , %edx ; movl X3 , %eax ; addl %edx , %eax ; movl %eax , X2 ; jmp .L1 ; .L0 : ; movl X4 , %edx ; movl X1 , %eax ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X5 ; movl X3 , %edx ; movl X5 , %eax ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X3 ; movl X6 , %edx ; movl X5 , %eax ; addl %edx , %eax ; movl %eax , X6 ; movl 0 , X2 ; .L1 : ; movl X4 , %eax ; negl %eax ; movl %eax , %edx ; movl X3 , %eax ; andl %edx , %eax ; movl %eax , X1 ; movl X3 , %edx ; movl X1 , %eax ; subl %eax , %edx ; movl %edx , %eax ; movl %eax , X5 ; movl X5 , %eax ; testl %eax , %eax ; jle .L2 ; movl X5 , %eax ; movl %eax , X2 ; .L2 : ;
movl X4 , %eax ; movl %eax , X3 ; movl X1 , %eax ; cmpl 128 , %eax ; jne .L0 ; movl 10 , X2 ; jmp .L2 ; .L0 : ; movl X1 , %eax ; cmpl 192 , %eax ; jne .L1 ; movl 12 , X2 ; jmp .L2 ; .L1 : ; movl 14 , X2 ; .L2 : ; movl X6 , %eax ; sall 24 , %eax ; movl %eax , %edx ; movl X7 , %eax ; sall 16 , %eax ; xorl %eax , %edx ; movl X8 , %eax ; sall 8 , %eax ; xorl %eax , %edx ; movl X9 , %eax ; xorl %edx , %eax ; movl %eax , X5 ;
movl X1 , %eax ; cmpl 128 , %eax ; jne .L2 ; jmp .L1 ; .L0 : ; movl X4 , %edx ; movl X5 , %eax ; xorl %edx , %eax ; movl %eax , X3 ; movl X7 , %edx ; movl X3 , %eax ; xorl %edx , %eax ; movl %eax , X6 ; movl X9 , %edx ; movl X6 , %eax ; xorl %edx , %eax ; movl %eax , X8 ; movl X2 , %eax ; addl 1 , %eax ; movl %eax , X2 ; .L1 : ; movl X2 , %eax ; cmpl 10 , %eax ; je .L0 ; .L2 : ; movl X1 , %eax ; cmpl 192 , %eax ; jne .L5 ; jmp .L4 ; .L3 : ; movl X4 , %edx ; movl X6 , %eax ; xorl %edx , %eax ; movl %eax , X8 ; movl X7 , %edx ; movl X8 , %eax ; xorl %edx , %eax ; movl %eax , X10 ; movl X9 , %edx ; movl X10 , %eax ; xorl %edx , %eax ; movl %eax , X11 ; movl X2 , %eax ; addl 1 , %eax ; movl %eax , X2 ; .L4 : ; movl X2 , %eax ; cmpl 8 , %eax ; je .L3 ; .L5 : ; movl X1 , %eax ; cmpl 256 , %eax ; jne .L8 ; jmp .L7 ; .L6 : ; movl X4 , %edx ; movl X10 , %eax ; xorl %edx , %eax ; movl %eax , X11 ; movl X7 , %edx ; movl X11 , %eax ; xorl %edx , %eax ; movl %eax , X12 ; movl X9 , %edx ; movl X12 , %eax ; xorl %edx , %eax ; movl %eax , X13 ; movl X2 , %eax ; addl 1 , %eax ; movl %eax , X2 ; .L7 : ; movl X2 , %eax ; cmpl 7 , %eax ; je .L6 ; .L8 : ;
