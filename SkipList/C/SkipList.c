
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>

struct Leaf { 
    int key; 
    int **pointers;
    int level;
};

typedef struct Leaf Leaf;


void printStructure(Leaf l)
{
    printf("%d\n", l.key);
}

int random_level(int max_level)
{
    srand(time(NULL));
    return rand()%max_level;
}

void generateOneLeaf(Leaf * a, int key, int max_level)
{    
    (*a).key = 10;
    (*a).level = random_level(max_level);
}

int main ()
{
    int size = 7;
    int i= 0;
    int max_level = (int)ceil(log(size));
    Leaf a[size];
    for (i = 0; i<size; i++)
    {
        generateOneLeaf(&a[i], 1, max_level);
    }

    printStructure(a[0]);
    return 0;

}