#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>

struct Leaf { 
    int key; 
    int level;
    int* pointers;

};

typedef struct Leaf Leaf;


void printStructure(Leaf l)
{
    int i=0;
    printf("key: %d\n", l.key);
    printf("level: %d\n", l.level);
    for(i = 0; i<l.level; i++)
    {
        printf("pointer: %p\n", l.pointers[i]);
    }
}

int random_level( int max_level)
{
    return (rand()%max_level+1);
}

void generateOneLeaf(Leaf * a, int key, int max_level)
{    
    int counter = 0;
    (*a).key = key;
    int level = random_level(max_level);
    (*a).level = level;
    (*a).pointers = (int*)malloc(sizeof(int*)*level);
}

void buildReference(Leaf* array, int size)
{
    int i = 0;
    int j = 0; 
    int k = 0;

    printf("%d\n", (*array).key);
    /*for (i = 0; i < size; i++)
    {
        for (j = 0; j<(*array[i]).level; j++)
        {
            for (k  = i+1; k<size; k++ )
            {
                if (array[k].level < j)
                {
                    array[i].pointers[j] = (array[k]);
                }
            }

            if (array[i].pointers[j] = 0)
            {
                array[i].pointers[j] = array[size];
            }
        }
    }*/
}
int main ()
{
    srand(time(NULL));
    int size = 7;
    int i= 0;
    int array[size];
    int max_level = (int)ceil(log2(size));

    array[0]=3;
    array[1]=5;
    array[2]=6;
    array[3]=20;
    array[4]=21;
    array[5]=25;
    array[6]=26;

    Leaf array_to_sort[size+1];
    for (i = 0; i<size; i++){
        generateOneLeaf(&array_to_sort[i], array[i], max_level);
        printStructure(array_to_sort[i]);
    }


    Leaf last;
    last.key = 10;
    last.level = max_level;
    array_to_sort[size] = last;

    return 0;

}