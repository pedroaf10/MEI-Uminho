package com.gamehub.Model.Users;

import com.fasterxml.jackson.annotation.JsonIgnore;

import javax.persistence.*;
import java.time.LocalDateTime;

@Entity
public class Mensagem {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private int id;

    private String conteudo;
    private LocalDateTime data;
    private Boolean lida;

    @JsonIgnore
    @ManyToOne(fetch = FetchType.EAGER)
    @JoinColumn(name = "caixamensagens_id")
    private CaixaMensagens caixaMensagens;

    @JsonIgnore
    @OneToOne(fetch = FetchType.LAZY)
    @JoinColumn(name = "remetente_id")
    private Gamer remetente;

    @Transient
    private int id_remetente;

    public Mensagem(int id, String conteudo, LocalDateTime data, Boolean lida, CaixaMensagens caixaMensagens, Gamer remetente) {
        this.id = id;
        this.conteudo = conteudo;
        this.data = data;
        this.lida = lida;
        this.caixaMensagens = caixaMensagens;
        this.remetente = remetente;
    }

    public Mensagem(String conteudo, CaixaMensagens caixaMensagens, Gamer remetente) {
        this.conteudo = conteudo;
        this.data = LocalDateTime.now();
        this.lida = false;
        this.caixaMensagens = caixaMensagens;
        this.remetente = remetente;
    }

    public Mensagem() {

    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public String getConteudo() {
        return conteudo;
    }

    public void setConteudo(String conteudo) {
        this.conteudo = conteudo;
    }

    public LocalDateTime getData() {
        return data;
    }

    public void setData(LocalDateTime data) {
        this.data = data;
    }

    public Boolean getLida() {
        return lida;
    }

    public void setLida(Boolean lida) {
        this.lida = lida;
    }

    public CaixaMensagens getCaixaMensagens() {
        return caixaMensagens;
    }

    public void setCaixaMensagens(CaixaMensagens caixaMensagens) {
        this.caixaMensagens = caixaMensagens;
    }

    public Gamer getRemetente() {
        return remetente;
    }

    public void setRemetente(Gamer remetente) {
        this.remetente = remetente;
    }

    public int getId_remetente() {
        return this.remetente.getId();
    }

    public void setId_remetente(int id_remetente) {
        this.id_remetente = id_remetente;
    }

    @Override
    public String toString() {
        return "Mensagem{" +
                "id=" + id +
                ", conteudo='" + conteudo + '\'' +
                ", data=" + data +
                ", lida=" + lida +
                ", caixaMensagens=" + caixaMensagens +
                ", remetente=" + remetente +
                '}';
    }
}
