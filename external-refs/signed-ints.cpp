#include <iostream>
#include <cstdint>

using namespace std;

#define STR(x) #x
#define PRINT(expr) (cout << STR(expr) << " = " << expr << endl)

int main()
{
    PRINT(INT64_MAX);
    PRINT(INT64_MIN);

    PRINT(- INT64_MAX);
    PRINT(- INT64_MIN);

    PRINT(INT64_MAX / -1);
    PRINT(INT64_MIN / -1);


    PRINT(-11 % 7);

    PRINT(INT64_MAX % -1);
    PRINT(INT64_MIN % -1);

    return 0;
}

