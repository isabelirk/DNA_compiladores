#Trabalho final de compiladores
#Isabeli Reik e Matheus Negrão - 2019/2

from Automato_lexico import Automato
from Producao import Producao
from Inuteis import Inuteis

automato = Automato()                              
automato.carrega('linguagem.txt')                       

#------------------------------------ Elimina Epsilon Transição ------------------------
class EpsilonTransicao(Automato):
    
    def __init__(self, automato):
        super(EpsilonTransicao, self).__init__()

        self.Estados = automato.Estados
        self.Alfabeto = automato.Alfabeto
        self.Finais = automato.Finais

    def imprimir(self):
        return super().imprimir('\nLIVRE DE EPSILON TRANSICOES:\n')

    def eliminarEpsilonTransicoes(self):
        self.buscarEpsilonTransicoes() 

    def buscarEpsilonTransicoes(self):        
        if super().EPSILON not in self.Alfabeto:
            return

        producoesComEpsilon = set()
        qtdEpsilon = len(producoesComEpsilon)
        qtdEstados = len(self.Estados) 
        idxEpsilon = self.Alfabeto
        i = 0

        #percorre os estados
        while i < qtdEstados: 
            #verifica se tem epsilon
            if i in self.Estados and len(self.Estados[i][super().EPSILON]) > 0:
                self.removerEpsilonTransicoes(i, self.Estados[i][super().EPSILON][0], producoesComEpsilon)
                qtdEstados = len(self.Estados) #atualiza qtd de estados
            i += 1

        self.removerEpsilonTransicoesEstados()

    def removerEpsilonTransicoes(self, transicaoOriginal, transicaoEpsilon, producoesComEpsilon):
        if len(self.Estados[transicaoOriginal][self.EPSILON]) > 0:

            for producao in list(self.Estados[transicaoEpsilon]):
                if producao != self.EPSILON and len(self.Estados[transicaoEpsilon][producao]) > 0:                    
                    self.Estados[transicaoEpsilon][producao] = (list(set(self.Estados[transicaoEpsilon][producao] + self.Estados[transicaoOriginal][producao])))                    
                    producoesComEpsilon.update(set(self.Estados[transicaoOriginal][self.EPSILON]))                    
        
        if len(self.Estados[transicaoEpsilon][self.EPSILON]) > 0:            
            if self.Estados[transicaoEpsilon][self.EPSILON][0] not in producoesComEpsilon:
                self.removerEpsilonTransicoes(transicaoEpsilon, self.Estados[transicaoEpsilon][self.EPSILON][0], producoesComEpsilon)

    def removerEpsilonTransicoesEstados(self):
        if self.EPSILON not in self.Alfabeto:
            return

        qtdEstados = len(self.Estados) 
        i = 0
        while i < qtdEstados: 
            if i in self.Estados:                    #verifica transição com epsilon
                self.Estados[i].pop(self.EPSILON)    #remove produção do epsilon
                qtdEstados = len(self.Estados)       #atualiza qtd estados
            i += 1

        self.Alfabeto.remove(self.EPSILON)

livreEpsilon = EpsilonTransicao(automato)           
livreEpsilon.eliminarEpsilonTransicoes()             #busca e faz tratamento do epsilon


#------------------------------------------- Determiniza -------------------------------
class Determinizacao(Automato):
    def __init__(self, automato):
        super(Determinizacao, self).__init__()

        self.Estados = automato.Estados
        self.Alfabeto = automato.Alfabeto
        self.Finais = automato.Finais
    
    def imprimir(self):                   #chama a função imprimir da classe pai
        return super().imprimir('\nDETERMINIZADO:\n')

    def determinizar(self): 
        self.buscarIndeterminismo()       #busca indeterminismos

    #add nova produção ao conjunto de estados finais
    def adicionaEstadoFinal(self, producoes, novaProducao): 
        for producao in producoes:          
            if producao in self.Finais:         #se é producão final
                self.Finais.add(novaProducao)   #add nova produção ao conjunto de finais

    #substitui um indeterminismo por string concatenando as transições
    def substituiNovaProducao(self):
        if len(self.NovosEstados) > 0:           #criadas novas produções na determinização
            for estado in self.Estados:                 #percorre estado do automato
                for simbolo in sorted(self.Alfabeto):          #percorre símbolos do alfabeto
                    if len(self.Estados[estado][simbolo]) > 1:       #se qtd de transições por uma prod for > 1
                        #gera uma produção agrupada para conhecer a origem da nova produção
                        producaoAgrupada = self.geraProducaoAgrupada(self.Estados[estado][simbolo]) 
                        #se essa produção estiver nas novas produções do automato recebe a nova produção gerada
                        if producaoAgrupada in self.NovosEstados:                
                            self.Estados[estado][simbolo] = [self.NovosEstados[producaoAgrupada][0]]    

    #percorre o autômato tratando seus indeterminismos
    def buscarIndeterminismo(self): 
        qtdEstados = len(self.Estados)   #marca a qtd inicial de estados
        i = 0              
        while i < qtdEstados:  
            for j in sorted(self.Alfabeto):     #percorre conjunto de símbolos do alfabeto
                if i in self.Estados and len(self.Estados[i][j]) > 1:    #se transição indeterminada:
                    self.determinizarProducao(self.Estados[i][j])        #determiniza  estado

                    qtdEstados = len(self.Estados)        #atualiza qtd de estados
            i += 1            

            if i == qtdEstados:     #se último estado
                for novoEstado in list(self.NovosEstados):          #percorre novas produções
                    #se não estiver no conjunto de estados do automato
                    if self.NovosEstados[novoEstado][0] not in self.Estados:   
                        self.determinizarProducao(self.NovosEstados[novoEstado][1])     #determiniza
                        qtdEstados = len(self.Estados)      #atualiza qtd de estados                     

    #determiniza x estado do automato
    def determinizarProducao(self, producoes): 
        estadoTemporario = dict()
        producaoAgrupada = self.geraProducaoAgrupada(producoes)

        #se a produção agrupada não existir nas novas produções ou nova regra não estiver no automato
        if ((producaoAgrupada not in self.NovosEstados) or (self.NovosEstados[producaoAgrupada][0] not in self.Estados)):  
            if (len(producoes) > 1) and (not self.existeProducaoAgrupada(producoes)):      #se tamanho for > 1 e não existe prod agrupada pra ela
                novoEstado = self.pegarNovoEstadoDetrminizacao()                              #pega o novo estado determinizado
                self.NovosEstados.update({self.geraProducaoAgrupada(producoes): [novoEstado,producoes]})    #coloca na estrutura de novos estados

            #percorre prod que contém indeterminação
            for i in producoes:  
                for j in sorted(self.Alfabeto):     #percorre conjunto de símbolos do alfabeto
                    if j in estadoTemporario:              #se símbolo j já estiver no estado temporário
                        #add a lista de transições de j
                        lista = list(set(estadoTemporario[j] + self.pegarProducaoOriginal(self.Estados[i][j]))) 
                        estadoTemporario[j] = lista        #ao estado criado

                        #se largura da lista for > 1 e não existe produção agrupada pra ela
                        if (len(lista) > 1) and (not self.existeProducaoAgrupada(lista)):  
                            novoEstado = self.pegarNovoEstadoDetrminizacao()              #enumera novo estado
                            self.NovosEstados.update({self.geraProducaoAgrupada(lista): [novoEstado,lista]})    #add aos novos estados

                    else:        #se símbolo j não estiver no estado temporário
                        producaoAtual = list(set(self.Estados[i][j]))      #concatena as transições de j

                        if len(producaoAtual) > 1:           #se tiver mais de uma prod
                            producaoAgrupadaTemp = self.geraProducaoAgrupada(producaoAtual)       #gera nova prod agrupada
                            if self.existeProducaoAgrupada(producaoAgrupadaTemp):          #se essa prod já existe
                                estadoTemporario.update({j: list(set(self.NovosEstados[producaoAgrupada][1]))}) #atualiza o estado temporário

                        #se não se essa produção não for nula e existe um estado para essa transição
                        elif (len(producaoAtual) > 0) and (self.existeNovoEstado(producaoAtual[0])):  
                            for prod in self.NovosEstados:              #percorre novos estados 
                                if self.NovosEstados[prod][0] == producaoAtual[0]:      #estado que for igual à transição
                                    estadoTemporario.update({j: list(set(self.NovosEstados[prod][1]))})      #atualiza
                        else:                                 
                            estadoTemporario.update({j: producaoAtual})    #add uma nova transição ao estado temporário

            self.setAlfabetoEstado(estadoTemporario);           #relaciona estado temporário com símbolos do alfabeto
            #add o estado temporário ao dict de estados da classe
            self.Estados.update({self.NovosEstados[producaoAgrupada][0]: estadoTemporario});  
             #verifica se deve add aos estados finais
            self.adicionaEstadoFinal(producoes, self.NovosEstados[producaoAgrupada][0])   
            self.substituiNovaProducao()     #verifica as produções criadas

    def geraProducaoAgrupada(self, lista):      #insere elementos de uma lista para uma string
        estado = ''
        for item in lista:      #para cada item da lista dada
            if estado == '':        #se for no inicio
                estado += str(item)     #concatena o item
            else:       #se for no meio
                estado += ',' + str(item)   #concatena com a virgula

        return estado                  

    def existeProducaoAgrupada(self, lista):        #verifica se lista dada já foi inserida em um estado novo
        retorno = False

        if len(lista) > 1:                                          #se o tamanho da lista dada for > 1
            producaoAgrupadaTemp = self.geraProducaoAgrupada(lista) #verifica pela sua possível produção agrupada
            return (producaoAgrupadaTemp in self.NovosEstados)
        else:         
            for i in self.NovosEstados:         #percorre os novos estados
                if lista[0] in self.NovosEstados[i][1]:       #verifica se a produção já existe
                    return True
        return retorno

    def pegarNovoEstadoDetrminizacao(self):     #add uma nova produção para contabilizar o novo tamanho do automato
        novasProducoes = []
        for producao in self.NovosEstados:      #pra cada produção dos novos estados
            novasProducoes.append(self.NovosEstados[producao][0])   #add um na contagem
        return len(set(list(self.Estados) + novasProducoes))     #retorna a qtd. Usa lista pra tratar repetições

    #retorna a produção que está na lista de estados novos a partir de uma prod do automato
    def pegarProducaoOriginal(self, producaoOrig):    
        retorno = list(set(producaoOrig))
        for producao in self.NovosEstados:
            for prod in producaoOrig:
                if self.NovosEstados[producao][0] == prod:
                    retorno = list(set(self.NovosEstados[producao][1]))

        return retorno

    def existeNovoEstado(self, producao):       #verifica se uma produção está no conjunto de novos estados
        if len(self.NovosEstados) > 0:
            for producaoAgrupada in self.NovosEstados:
                if self.NovosEstados[producaoAgrupada][0] == producao:
                    return True

        return False

determinizado = Determinizacao(automato) 
determinizado.determinizar()                   


#-------------------------------------- Elimina estados inalcançaveis -------------------------- 
class Inalcancaveis(Inuteis):
    
    def __init__(self, automato):
        super(Inalcancaveis, self).__init__(automato)

    def imprimir(self):
        return super().imprimir('\nSEM INALCANCAVEIS:\n')
          
    def removerInalcancaveis(self):
        estados = self.gerarEstadosParaMinimizacao()
        #passa 0 fixo pois para remover os inalcançáveis parte do estado incial
        self.visitaNovaProducaoInalcancavel(estados, 0) 

    def visitaNovaProducaoInalcancavel(self, estados, transicao):
         if transicao in estados:
             if transicao in self.Finais:              #se a transição for um estado final
                 #add no automato pois pelo estado inicial o atual é alcançado
                 self.adicionaAutomatoMinimizado(transicao,-1,-1)   

             #percorre todas as produções daquela transição e então segue com busca em profundidade
             for producao in estados[transicao]: 
                 #caso não tenha uma produção válida finaliza a recursão atual    
                if not estados[transicao][producao].temProducao():  
                    continue
                #Se a produção já foi visitada, finaliza a recursão atual
                if estados[transicao][producao].visitado: 
                    return
        
                estados[transicao][producao].visitado = True
                #add a produção no automato
                self.adicionaAutomatoMinimizado(transicao,producao,estados[transicao][producao].producao); 
                #busca recursivamente o estado final
                self.visitaNovaProducaoInalcancavel(estados, estados[transicao][producao].producao);  

semInalcancaveis = Inalcancaveis(automato)
semInalcancaveis.removerInalcancaveis()    


#------------------------------ Elimina os estados mortos ------------------------------------ 
class Mortos(Inuteis):
    
    def __init__(self, automato):
        super(Mortos, self).__init__(automato)
    
    def imprimir(self):
        return super().imprimir('DETERMINIZADO, LIVRE DE EPSILON TRANSIÇÃO, MORTOS E INALCANÇAVÉIS:\n')

    def removerMortos(self):
        estados = self.gerarEstadosParaMinimizacao()
        self.AutomatoMinimizado = dict()
        for transicao in estados:
            for producao in estados[transicao]:
                self.visitaNovaProducaoMortos(estados, transicao)
                estados[transicao][producao].chegouEstadoTerminal = self.adicionaAutomatoMinimizado(transicao,producao,estados[transicao][producao].producao)
    
    def visitaNovaProducaoMortos(self, estados, transicao):
        if transicao in estados:
            if (transicao in self.Finais) and (estados[transicao] == {}) :
                self.adicionaAutomatoMinimizado(transicao,-1,-1)
                return True

            for producao in estados[transicao]:
                if estados[transicao][producao].chegouEstadoTerminal or (transicao in self.Finais):
                    return True
                if not estados[transicao][producao].temProducao():      
                    return False
                if estados[transicao][producao].visitado:
                    continue
                
            estados[transicao][producao].visitado = True
            if self.visitaNovaProducaoMortos(estados, estados[transicao][producao].producao):
                estados[transicao][producao].chegouEstadoTerminal = True
                self.adicionaAutomatoMinimizado(transicao,producao,estados[transicao][producao].producao)
                return True

        return False

semMortos = Mortos(semInalcancaveis)      
semMortos.removerMortos()                 
semMortos.imprimir()