// This line is necessary to be able to output information to the screen
#include <iostream>

// The program starts here and carries on line by line
int main()
{
    // Create two integers a and b containing 10 and 5
    int a = 10;
    int b = 5;

    /* Add them together and store the result in another
       integer called sum */
    int sum = a + b;

    // Output the sum to the screen
    std::cout << sum << std::endl;

    // End the program and send a value of 0 (success) back
    // to the operating system
    return 0;
}
