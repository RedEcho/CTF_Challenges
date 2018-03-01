int PrintFlag(int* flagAddress) {
    return printf("%d%d%d%d%d\n", *flagAddress, *(flagAddress + 0x4), *(flagAddress + 0x8), *(flagAddress + 0xc), *(flagAddress + 0x10));
    // here we can see the order of the characters. 
    // The PrintFlag() function is called with the address (Stack Pointer - 32) line 51. So (Stack Pointer - 32) must be the first character
    // Then, it looks 4 bytes ahead for the second character, so (Stack Pointer - 32 + 4 = Stack Pointer - 28) must be the second character
    // And so on...
}


int SIGINTHandler(int argc) {
    signal(0x2, 0x4007f1);
    puts("\n You thought you could avoid it huh?");
    fflush(*stdout@@GLIBC_2.2.5);
    /* rax = *target;
    remove(rax); */ // Once again, this target memory is a mystery for me.
    return rax;
}


int main(int argc, char** argv) {

    // Variables declared in memory. I did choose sensible names, thanks to the PrintFlag function()
    userInput:  // Address = Stack Pointer -8
    char5:      // Address = Stack Pointer -16
    char4:      // Address = Stack Pointer -20
    char3:      // Address = Stack Pointer -24
    char2:      // Address = Stack Pointer -28
    char1:      // Address = Stack Pointer -32
    var_24:     // Address = Stack Pointer -36
    inputAddress:// Address = Stack Pointer -48

    int returnValue;
    inputAdress = argv;

    signal(2, *SIGINTHandler()); // signal needs a pointer to the function that is supposed to handle the signal, in our case SIGINTHandler()
    // *target = *inputAddress;  // No freakin idea what this target memory is for, so just comment out.
    if (argc != 2) { // No argument? then return 2
            returnValue = 2;
    }
    else {
            userInput = *(inputAddress + 0x8); // the user's input is at argv[1]
            char1 = userInput & 0xff) + 1;              // we only keep the last 8 bits of the first letter, and add 1 to it.
            char2 = (userInput + 0x1) & 0xff) + 2;      // same with every other letters
            char3 = (userInput + 0x2) & 0xff) + 3;
            char4 = (userInput + 0x3) & 0xff) + 4;
            char5 = (userInput + 0x4) & 0xff) + 5;
            if (((char4 == 0x6f) && (char3 == char4 + 0xe)) && (char1 == char5 - 0xa)) {
                    if (char2 == 0x35) {
                            if (char5 == char4 + 0x3) {
                                    printf("Now here is your flag: ");
                                    PrintFlag(&char1); // We send the address of char1, and it PrintFlag() will find the other characters from there.
                                    returnValue = 1;
                            }
                            else {
                                    sleep(0x2);
                                    remove(*inputAddress); // And that apparently is the line that deletes the binary file... somehow.
                                    puts("successfully deleted!");
                                    returnValue = 2;
                            }
                    }
                    else {
                            sleep(0x2);
                            remove(*inputAddress);
                            puts("successfully deleted!");
                            returnValue = 2;
                    }
            }
            else {
                    sleep(0x2);
                    remove(*inputAddress);
                    puts("successfully deleted!");
                    returnValue = 2;
            }
    }
    return returnValue;
}
