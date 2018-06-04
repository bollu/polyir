const int N = 10;
void foo(int A[N][N]) {
    for (int i = 0; i < N; i+=10) {
        for(int j = 0; j < N; j++) {
            const int val = i + j;
            A[i][j] = val;
        }
    }
}
