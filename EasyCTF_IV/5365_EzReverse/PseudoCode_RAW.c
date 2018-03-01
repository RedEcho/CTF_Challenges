int _Z7print_5Pi(int * arg0) {
    rax = printf("%d%d%d%d%d\n", *(int32_t *)arg0, *(int32_t *)(arg0 + 0x4), *(int32_t *)(arg0 + 0x8), *(int32_t *)(arg0 + 0xc), *(int32_t *)(arg0 + 0x10));
    return rax;
}

int _Z13sigintHandleri(int arg0) {
    signal(0x2, 0x4007f1);
    puts("\n You thought you could avoid it huh?");
    fflush(*stdout@@GLIBC_2.2.5);
    rax = *target;
    rax = remove(rax);
    return rax;
}

int main(int arg0, int arg1) {

        ; Variables:
        ;    var_8: -8
        ;    var_10: -16
        ;    var_14: -20
        ;    var_18: -24
        ;    var_1C: -28
        ;    var_20: -32
        ;    var_24: -36
        ;    var_30: -48

    var_30 = arg1;
    signal(0x2, 0x4007f1);
    *target = *var_30;
    if (arg0 != 0x2) {
            rax = 0x2;
    }
    else {
            var_8 = *(var_30 + 0x8);
            var_20 = sign_extend_64(*(int8_t *)var_8 & 0xff) + 0x1;
            var_1C = sign_extend_64(*(int8_t *)(var_8 + 0x1) & 0xff) + 0x2;
            var_18 = sign_extend_64(*(int8_t *)(var_8 + 0x2) & 0xff) + 0x3;
            var_14 = sign_extend_64(*(int8_t *)(var_8 + 0x3) & 0xff) + 0x4;
            var_10 = sign_extend_64(*(int8_t *)(var_8 + 0x4) & 0xff) + 0x5;
            if (((var_14 == 0x6f) && (var_18 == var_14 + 0xe)) && (var_20 == var_10 - 0xa)) {
                    if (var_1C == 0x35) {
                            if (var_10 == var_14 + 0x3) {
                                    printf("Now here is your flag: ");
                                    print_5(&var_20);
                                    rax = 0x1;
                            }
                            else {
                                    puts("successfully deleted!");
                                    rax = 0x2;
                            }
                    }
                    else {
                            puts("successfully deleted!");
                            rax = 0x2;
                    }
            }
            else {
                    puts("successfully deleted!");
                    rax = 0x2;
            }
    }
    return rax;
}
