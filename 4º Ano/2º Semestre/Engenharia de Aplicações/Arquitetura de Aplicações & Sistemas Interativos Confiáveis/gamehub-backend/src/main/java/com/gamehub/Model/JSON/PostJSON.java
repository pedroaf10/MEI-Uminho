package com.gamehub.Model.JSON;

import com.fasterxml.jackson.annotation.JsonProperty;

import java.util.List;

public class PostJSON {

    private String jogo;
    private String descricao;
    private List<Integer> tags;
    private String multimedia;
    private String idioma;
    private String modoJogo;
    private int participantes;
    private String nomeEquipa;
    private String plataforma;

    public PostJSON(@JsonProperty("jogo") String jogo,
                    @JsonProperty("descricao") String descricao,
                    @JsonProperty("tags") List<Integer> tags,
                    @JsonProperty("multimedia") String multimedia,
                    @JsonProperty("idioma") String idioma,
                    @JsonProperty("modoJogo") String modoJogo,
                    @JsonProperty("participantes") int participantes,
                    @JsonProperty("nomeEquipa") String nomeEquipa,
                    @JsonProperty("plataforma") String plataforma) {
        this.jogo = jogo;
        this.descricao = descricao;
        this.tags = tags;
        this.multimedia = multimedia;
        this.idioma = idioma;
        this.modoJogo = modoJogo;
        this.participantes = participantes;
        this.nomeEquipa = nomeEquipa;
        this.plataforma = plataforma;
    }

    public String getJogo() {
        return jogo;
    }

    public void setJogo(String jogo) {
        this.jogo = jogo;
    }

    public String getDescricao() {
        return descricao;
    }

    public void setDescricao(String descricao) {
        this.descricao = descricao;
    }

    public List<Integer> getTags() {
        return tags;
    }

    public void setTags(List<Integer> tags) {
        this.tags = tags;
    }

    public String getMultimedia() {
        return multimedia;
    }

    public void setMultimedia(String multimedia) {
        this.multimedia = multimedia;
    }

    public String getIdioma() {
        return idioma;
    }

    public void setIdioma(String idioma) {
        this.idioma = idioma;
    }

    public String getModoJogo() {
        return modoJogo;
    }

    public void setModoJogo(String modoJogo) {
        this.modoJogo = modoJogo;
    }

    public int getParticipantes() {
        return participantes;
    }

    public void setParticipantes(int participantes) {
        this.participantes = participantes;
    }

    public String getNomeEquipa() {
        return nomeEquipa;
    }

    public void setNomeEquipa(String nomeEquipa) {
        this.nomeEquipa = nomeEquipa;
    }

    public String getPlataforma() {
        return plataforma;
    }

    public void setPlataforma(String plataforma) {
        this.plataforma = plataforma;
    }
}
