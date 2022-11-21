package com.gamehub.Model.Users;


import javax.persistence.*;
import java.util.ArrayList;
import java.util.List;

@Entity
public class CaixaMensagens {
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private int Id;


    @OneToMany(mappedBy = "caixaMensagens", cascade = CascadeType.ALL, fetch = FetchType.EAGER)
    private List<Mensagem> mensagens;

    public CaixaMensagens(int id, List<Mensagem> mensagens) {
        Id = id;
        this.mensagens = mensagens;
    }

    public CaixaMensagens() {
        this.mensagens = new ArrayList<>();
    }

    public int getId() {
        return Id;
    }

    public void setId(int id) {
        Id = id;
    }

    public List<Mensagem> getMensagens() {
        return mensagens;
    }

    public void setMensagens(List<Mensagem> mensagens) {
        this.mensagens = mensagens;
    }

    @Override
    public String toString() {
        return "CaixaMensagens{" +
                "Id=" + Id +
                ", mensagens=" + mensagens +
                '}';
    }

    /**
     * Adiciona uma mensagem à caixa de mensagem
     * @param m Mensagem a adicionar
     */
    public void addMensagem(Mensagem m) {
        this.mensagens.add(m);
    }
}
