import subprocess
import string
from itertools import product
from sys import exit
from tqdm import tqdm

guess = ""
chars = string.ascii_letters + string.digits
guessLength = 0

print("\n\nBruteforce attack")
print("-----------------\n")

while True:
    guessLength = guessLength + 1
    expectedGuesses = len(chars) ** guessLength

    print("\nTrying every", guessLength, "character long argument")

    with tqdm(total = expectedGuesses, mininterval = 1) as pbar:
        for guess in product(chars, repeat=guessLength):
            pbar.update(1)

            guess = ''.join(guess)

            exec = subprocess.run(["./PATCHED_executable", guess], stdout=subprocess.PIPE)
            output = exec.stdout.decode('utf-8')
            if not 'deleted!' in output: 
                print("ARGUMENT FOUND\n", guess, "\tOutput = ", output)
                exit()
            # else:
            #     print(guess, "\tOutput = ", output[:-1])

