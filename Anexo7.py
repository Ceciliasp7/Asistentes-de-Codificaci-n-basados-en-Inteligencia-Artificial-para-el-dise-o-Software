def merge_sort(lista):

    if len(lista) > 1:
    
        medio = len(lista) // 2
        izquierda = lista[:medio]
        derecha = lista[medio:]

        # Llamada recursiva para ordenar las sublistas
        merge_sort(izquierda)
        merge_sort(derecha)

        # Combinar las sublistas ordenadas
        i, j, k = 0, 0, 0
        while i < len(izquierda) and j < len(derecha):
            if izquierda[i] < derecha[j]:
                lista[k] = izquierda[i]
                i += 1
            else:
                lista[k] = derecha[j]
                j += 1
            k += 1

        while i < len(izquierda):
            lista[k] = izquierda[i]
            i += 1
            k += 1

        while j < len(derecha):
            lista[k] = derecha[j]
            j += 1
            k += 1


# Ejemplo de uso

if __name__ == "__main__":

    lista_ejemplo = [38, 27, 43, 3, 9, 82, 10]
    merge_sort(lista_ejemplo)
    print("Lista ordenada:", lista_ejemplo)
