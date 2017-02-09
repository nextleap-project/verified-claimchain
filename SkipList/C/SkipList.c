#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>

struct LL
{
struct Leaf * leaf;
struct LL * pointer;
};

typedef struct LL LL;

struct Leaf { 
int key; 
int level;
LL* pointers;

};

typedef struct Leaf Leaf;

int random_level( int max_level)
{
return (rand()%max_level+1);
}

Leaf* generateOneLeaf(int key, int max_level)
{ 
int levels = random_level(max_level);
LL* pointers = (LL*)malloc(sizeof(LL)*levels);

Leaf* leaf = (Leaf*)(malloc(sizeof(Leaf)));
(*leaf).key = key;
(*leaf).level = levels;
(*leaf).pointers = pointers;

return leaf;
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

LL* llheap = (LL *)malloc(sizeof (LL)*max_level);
Leaf* heap = (Leaf*)malloc(sizeof (Leaf));
heap->key = 0;
heap->level = max_level;
heap->pointers = llheap;

Leaf* current = heap;

for (i =0; i<size; i++)
{
Leaf* newLeaf= generateOneLeaf(array[i],max_level);
((current->pointers)[0]).leaf = newLeaf;
current = newLeaf;
}

return 0;

}