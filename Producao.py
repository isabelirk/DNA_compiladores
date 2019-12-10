#Trabalho final de compiladores
#Isabeli Reik e Matheus Negrão - 2019/2

class Producao():
    producao = 0
    visitado = False

    def __init__(self, producao):
       self.producao = producao
       self.visitado = False
       self.chegouEstadoTerminal = False

    def temProducao(self):
        return self.producao >= 0
