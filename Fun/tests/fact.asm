.text
	beqz $a0, init_end
	lw $a0, 0($a1)
	jal atoi
	la $t0, arg
	sw $v0, 0($t0)
init_end:
	li $t0, 4
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	li $t0, 1
	addi $sp, $sp, 4
	lw $t1, 0($sp)
	mul $t0, $t0, $t1
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	jal malloc
	addi $sp, $sp, 4
	la $t1, fact_1
	sw $t0, 0($t1)
	la $t0, fun_fact_0
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	li $t0, 4
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	li $t0, 0
	addi $sp, $sp, 4
	lw $t1, 0($sp)
	mul $t0, $t0, $t1
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	la $t0, fact_1
	lw $t0, 0($t0)
	addi $sp, $sp, 4
	lw $t1, 0($sp)
	add $t0, $t0, $t1
	addi $sp, $sp, 4
	lw $t1, 0($sp)
	sw $t1, 0($t0)
	la $t0, fact_1
	lw $t0, 0($t0)
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	li $t0, 6
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	li $t0, 4
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	li $t0, 0
	addi $sp, $sp, 4
	lw $t1, 0($sp)
	mul $t0, $t0, $t1
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	la $t0, fact_1
	lw $t0, 0($t0)
	addi $sp, $sp, 4
	lw $t1, 0($sp)
	add $t0, $t0, $t1
	lw $t0, 0($t0)
	jalr $t0
	addi $sp, $sp, 8
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	jal print_int
	addi $sp, $sp, 4
	li $v0, 10
	syscall
malloc:
	sw $fp, 0($sp)
	subi $sp, $sp, 4
	sw $ra, 0($sp)
	subi $sp, $sp, 4
	addi $fp, $sp, 8
	addi $sp, $sp, 0
	lw $t0, 4($fp)
	move $a0, $t0
	li $v0, 9
	syscall
	move $t0, $v0
	move $sp, $fp
	lw $ra, -4($fp)
	lw $fp, 0($fp)
	jr $ra
	li $t0, 0
	move $sp, $fp
	lw $ra, -4($fp)
	lw $fp, 0($fp)
	jr $ra
fun_fact_0:
	sw $fp, 0($sp)
	subi $sp, $sp, 4
	sw $ra, 0($sp)
	subi $sp, $sp, 4
	addi $fp, $sp, 8
	addi $sp, $sp, -4
	li $t0, 1
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	lw $t0, 4($fp)
	addi $sp, $sp, 4
	lw $t1, 0($sp)
	sle $t0, $t0, $t1
	bnez $t0, __label_0
	lw $t0, 8($fp)
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	li $t0, 1
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	lw $t0, 4($fp)
	addi $sp, $sp, 4
	lw $t1, 0($sp)
	sub $t0, $t0, $t1
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	li $t0, 4
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	li $t0, 0
	addi $sp, $sp, 4
	lw $t1, 0($sp)
	mul $t0, $t0, $t1
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	lw $t0, 8($fp)
	addi $sp, $sp, 4
	lw $t1, 0($sp)
	add $t0, $t0, $t1
	lw $t0, 0($t0)
	jalr $t0
	addi $sp, $sp, 8
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	lw $t0, 4($fp)
	addi $sp, $sp, 4
	lw $t1, 0($sp)
	mul $t0, $t0, $t1
	sw $t0, -8($fp)
	b __label_1
__label_0:
	li $t0, 1
	sw $t0, -8($fp)
__label_1:
	lw $t0, -8($fp)
	move $sp, $fp
	lw $ra, -4($fp)
	lw $fp, 0($fp)
	jr $ra
	li $t0, 0
	move $sp, $fp
	lw $ra, -4($fp)
	lw $fp, 0($fp)
	jr $ra
#built-in atoi
atoi:
	move $t0, $a0
	li $t1, 0
	li $t2, 10
atoi_loop:
	lbu $t3, 0($t0)
	beq $t3, $zero, atoi_end
	li $t4, 48
	blt $t3, $t4, atoi_error
	li $t4, 57
	bgt $t3, $t4, atoi_error
	addi $t3, $t3, -48
	mul $t1, $t1, $t2
	add $t1, $t1, $t3
	addi $t0, $t0, 1
	b atoi_loop
atoi_error:
	li $v0, 10
	syscall
atoi_end:
	move $v0, $t1
	jr $ra
#built-in print_int
print_int:
	lw $a0, 4($sp)
	li $v0, 1
	syscall
	sw $a0, 0($sp)
	subi $sp, $sp, 4
	jr $ra
#built-in power
power:
	lw $s0, 8($sp)
	lw $s1, 4($sp)
	li $t0, 1
	b power_loop_guard
power_loop_code:
	mul $t0, $t0, $s1
	subi $s0, $s0, 1
power_loop_guard:
	bgtz $s0, power_loop_code
	sw $t0, 0($sp)
	subi $sp, $sp, 4
	jr $ra
.data
fact_1:
	.word 0
arg:
	.word 0
