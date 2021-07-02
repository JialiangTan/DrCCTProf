#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

int main()
{

void *t1_arr;
int32_t *t2_arr;

int l = 4;
t2_arr = (int32_t *) malloc(4 * sizeof(int32_t));
t1_arr = (void *) t2_arr;

for (int i = 0; i < l; i++)
{
    t2_arr[i] = i;
    *(t2_arr + i) = i;
    printf("%d: int:%p void:%p\n", i, t2_arr + i, t1_arr + i);
}

}
