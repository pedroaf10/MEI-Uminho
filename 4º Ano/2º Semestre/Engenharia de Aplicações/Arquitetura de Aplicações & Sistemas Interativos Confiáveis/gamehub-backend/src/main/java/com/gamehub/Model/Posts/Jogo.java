package com.gamehub.Model.Posts;

import javax.persistence.*;
import java.util.List;

@Entity
public class Jogo {
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private int id;
    private String nome;


    @ManyToMany(fetch = FetchType.LAZY)
    @JoinColumn(name = "plataforma_id")
    private List<Plataforma> plataformas;


    @ManyToMany(fetch = FetchType.EAGER)
    @JoinColumn(name = "tag_id")
    private List<Tag> tags;

    private int faixaEtaria;
    private int anoLancamento;
    private String desenvolvedora;

    private String bannerLink;

    public Jogo(int id, String nome, List<Plataforma> plataformas, List<Tag> tags, int faixaEtaria, int anoLancamento, String desenvolvedora, String banner) {
        this.id = id;
        this.nome = nome;
        this.plataformas = plataformas;
        this.tags = tags;
        this.faixaEtaria = faixaEtaria;
        this.anoLancamento = anoLancamento;
        this.desenvolvedora = desenvolvedora;
        this.bannerLink = banner;
    }

    public Jogo() {

    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public String getNome() {
        return nome;
    }

    public void setNome(String nome) {
        this.nome = nome;
    }

    public int getFaixaEtaria() {
        return faixaEtaria;
    }

    public void setFaixaEtaria(int faixaEtaria) {
        this.faixaEtaria = faixaEtaria;
    }

    public int getAnoLancamento() {
        return anoLancamento;
    }

    public void setAnoLancamento(int anoLancamento) {
        this.anoLancamento = anoLancamento;
    }

    public String getDesenvolvedora() {
        return desenvolvedora;
    }

    public void setDesenvolvedora(String desenvolvedora) {
        this.desenvolvedora = desenvolvedora;
    }


    public List<Plataforma> getPlataformas() {
        return plataformas;
    }

    public void setPlataformas(List<Plataforma> plataformas) {
        this.plataformas = plataformas;
    }

    public List<Tag> getTags() {
        return tags;
    }

    public void setTags(List<Tag> tags) {
        this.tags = tags;
    }

    public String getBannerLink() {
        return bannerLink;
    }

    public void setBannerLink(String bannerLink) {
        this.bannerLink = bannerLink;
    }

    @Override
    public String toString() {
        return "Jogo{" +
                "id=" + id +
                ", nome='" + nome + '\'' +
                ", tags=" + tags +
                ", faixaEtaria=" + faixaEtaria +
                ", anoLancamento=" + anoLancamento +
                ", desenvolvedora='" + desenvolvedora + '\'' +
                '}';
    }
}
