.text
.global root, control
.type root,@function
root:
    mov $17, %rdi
    mov $51, %r8
    call control
    mov %rax, %rdi
    mov $60, %rax
    syscall
.size root,.-root
.type control,@function
control:
    mov %r8, %rax
    ret
    .rept 24
    nop
    .endr
.size control,.-control
.section .note.GNU-stack,"",@progbits
