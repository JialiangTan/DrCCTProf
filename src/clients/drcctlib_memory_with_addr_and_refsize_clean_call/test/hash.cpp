#include <stdio.h>
#include <cstdint>

int hashvar(uint64_t cur, uint64_t old){
    uint64_t key = old;
    uint64_t hash = key << 32;
    key = cur;
    hash |= key;
    printf("hash %lu\n", hash);
    printf("cur %lu\n", cur);
    printf("old %lu\n", old);
    printf("=================\n");

    uint64_t ctx1 = hash >> 32;
    uint64_t ctx2 = hash & 0xffffffff;
    printf("context1 %lu\n", ctx1);
    printf("context2 %lu\n", ctx2);


}

int main(){
    hashvar(100, 10000);
}
