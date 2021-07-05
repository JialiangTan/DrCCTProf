#include<iostream>
using namespace std;
int main(){
    int l = 10;
    int *array = (int *) malloc(l*sizeof(int));
    //printf("%p %p\n", array, array+l);
    for (int i = 0; i < l; i++){
        array[i] = i;
        printf("%p\n", array + i);
    }
    return 0;
}
