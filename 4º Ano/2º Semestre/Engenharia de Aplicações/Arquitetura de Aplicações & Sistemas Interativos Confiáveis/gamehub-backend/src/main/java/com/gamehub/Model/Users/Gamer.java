package com.gamehub.Model.Users;


import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.gamehub.Model.Posts.Grupo;
import com.gamehub.Model.Posts.Jogo;
import com.gamehub.Model.Posts.PostGrupo;
import com.gamehub.Model.Posts.PostMultimedia;

import javax.persistence.*;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

@Entity
public class Gamer {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private int id;
    private float classificacao;

    @JsonIgnore
    private LocalDateTime data_nascimento;

    @JsonIgnore
    private int numero_classificacoes;

    private String nome;
    private String estado;

    @JsonIgnore
    @OneToOne(mappedBy = "gamer", cascade = CascadeType.ALL, fetch = FetchType.EAGER)
    private Utilizador utilizador;

    @ManyToOne(fetch = FetchType.EAGER, cascade = CascadeType.ALL)
    @JoinColumn(name = "avatar_id")
    private Avatar avatar;

    @ManyToMany(cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    @JoinTable(name = "recompensas",
            joinColumns = @JoinColumn(name = "gamer", referencedColumnName = "id"),
            inverseJoinColumns = @JoinColumn(name = "recompensa",
                    referencedColumnName = "id"))
    private List<Recompensa> recompensas;

    @JsonIgnoreProperties({"amigos", "classificacao", "numero_classificacoes", "utilizador", "recompensas", "jogos", "caixasMensagens", "likedPosts", "dislikedPosts", "publicacoes_grupo", "publicacoes_media", "grupo"})
    @ManyToMany(cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    @JoinTable(name = "amigos",
            joinColumns = @JoinColumn(name = "amigo1", referencedColumnName = "id"),
            inverseJoinColumns = @JoinColumn(name = "amigo2",
                    referencedColumnName = "id"))
    private List<Gamer> amigos;

    @JsonIgnore
    @ManyToMany(cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    @JoinTable(name = "jogos",
            joinColumns = @JoinColumn(name = "gamer", referencedColumnName = "id"),
            inverseJoinColumns = @JoinColumn(name = "jogo",
                    referencedColumnName = "id"))
    private List<Jogo> jogos;


    @JsonIgnore
    @ManyToMany(cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    @JoinTable(name = "conversas",
            joinColumns = @JoinColumn(name = "gamer", referencedColumnName = "id"),
            inverseJoinColumns = @JoinColumn(name = "caixaMensagens",
                    referencedColumnName = "id"))
    private List<CaixaMensagens> caixasMensagens;

    @JsonIgnore
    @ManyToMany(cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    @JoinTable(name = "likes",
            joinColumns = @JoinColumn(name = "gamer", referencedColumnName = "id"),
            inverseJoinColumns = @JoinColumn(name = "post",
                    referencedColumnName = "id"))
    private List<PostMultimedia> likedPosts;

    @JsonIgnore
    @ManyToMany(cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    @JoinTable(name = "dislikes",
            joinColumns = @JoinColumn(name = "gamer", referencedColumnName = "id"),
            inverseJoinColumns = @JoinColumn(name = "post",
                    referencedColumnName = "id"))
    private List<PostMultimedia> dislikedPosts;

    @JsonIgnore
    @OneToMany(mappedBy = "gamer", cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    private List<PostGrupo> publicacoes_grupo;

    @JsonIgnore
    @OneToMany(mappedBy = "gamer", cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    private List<PostMultimedia> publicacoes_media;

    @JsonIgnore
    @ManyToOne(fetch = FetchType.LAZY)
    @JoinColumn(name = "grupo_id")
    private Grupo grupo;

    @JsonIgnore
    @ManyToMany(cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    @JoinTable(name = "possiveis_avaliacoes",
            joinColumns = @JoinColumn(name = "amigo1", referencedColumnName = "id"),
            inverseJoinColumns = @JoinColumn(name = "amigo2",
                    referencedColumnName = "id"))
    private List<Gamer> possiveisAvaliacoes;


    public Gamer(int id, float classificacao, int numero_classificacoes, String nome, String estado, Utilizador utilizador, Avatar avatar, List<Recompensa> recompensas, List<Gamer> amigos, List<Gamer> possiveisAvaliacoes, List<Jogo> jogos, List<CaixaMensagens> caixasMensagens, List<PostGrupo> publicacoes_grupo, List<PostMultimedia> publicacoes_media, Grupo grupo, LocalDateTime data_nascimento) {
        this.id = id;
        this.classificacao = classificacao;
        this.numero_classificacoes = numero_classificacoes;
        this.nome = nome;
        this.estado = estado;
        this.utilizador = utilizador;
        this.avatar = avatar;
        this.recompensas = recompensas;
        this.amigos = amigos;
        this.possiveisAvaliacoes = possiveisAvaliacoes;
        this.jogos = jogos;
        this.caixasMensagens = caixasMensagens;
        this.publicacoes_grupo = publicacoes_grupo;
        this.publicacoes_media = publicacoes_media;
        this.grupo = grupo;
        this.data_nascimento = data_nascimento;
    }

    public Gamer() {

    }

    public Gamer(String nickname, LocalDateTime data_nascimento) {
        this.classificacao = 5;
        this.numero_classificacoes = 1;
        this.nome = nickname;
        this.estado = "Online";
        this.recompensas = new ArrayList<>();
        this.amigos = new ArrayList<>();
        this.jogos = new ArrayList<>();
        this.publicacoes_grupo = new ArrayList<>();
        this.publicacoes_media = new ArrayList<>();
        this.caixasMensagens = new ArrayList<>();
        this.likedPosts = new ArrayList<>();
        this.dislikedPosts = new ArrayList<>();
        this.possiveisAvaliacoes = new ArrayList<>();
        //this.avatar = new Avatar("https://robohash.org/" + nickname);
        this.data_nascimento = data_nascimento;
        this.avatar = new Avatar("https://api.multiavatar.com/" + nickname + ".png");
    }

    public int getNumero_classificacoes() {
        return numero_classificacoes;
    }

    public void setNumero_classificacoes(int numero_classificacoes) {
        this.numero_classificacoes = numero_classificacoes;
    }

    public List<CaixaMensagens> getCaixasMensagens() {
        return caixasMensagens;
    }

    public void setCaixasMensagens(List<CaixaMensagens> caixasMensagens) {
        this.caixasMensagens = caixasMensagens;
    }

    public List<PostMultimedia> getLikedPosts() {
        return likedPosts;
    }

    public void setLikedPosts(List<PostMultimedia> likedPosts) {
        this.likedPosts = likedPosts;
    }

    public List<PostMultimedia> getDislikedPosts() {
        return dislikedPosts;
    }

    public void setDislikedPosts(List<PostMultimedia> dislikedPosts) {
        this.dislikedPosts = dislikedPosts;
    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public float getClassificacao() {
        return classificacao;
    }

    public void setClassificacao(float classificacao) {
        this.classificacao = classificacao;
    }

    public String getNome() {
        return nome;
    }

    public void setNome(String nome) {
        this.nome = nome;
    }

    public String getEstado() {
        return estado;
    }

    public void setEstado(String estado) {
        this.estado = estado;
    }

    public Utilizador getUtilizador() {
        return utilizador;
    }

    public void setUtilizador(Utilizador utilizador) {
        this.utilizador = utilizador;
    }

    public Avatar getAvatar() {
        return avatar;
    }

    public void setAvatar(Avatar avatar) {
        this.avatar = avatar;
    }

    public List<Recompensa> getRecompensas() {
        return recompensas;
    }

    public void setRecompensas(List<Recompensa> recompensas) {
        this.recompensas = recompensas;
    }

    public List<Gamer> getAmigos() {
        return amigos;
    }

    public void setAmigos(List<Gamer> amigos) {
        this.amigos = amigos;
    }

    public List<Jogo> getJogos() {
        return jogos;
    }

    public void setJogos(List<Jogo> jogos) {
        this.jogos = jogos;
    }

    public List<PostGrupo> getPublicacoes_grupo() {
        return publicacoes_grupo;
    }

    public void setPublicacoes_grupo(List<PostGrupo> publicacoes_grupo) {
        this.publicacoes_grupo = publicacoes_grupo;
    }

    public List<PostMultimedia> getPublicacoes_media() {
        return publicacoes_media;
    }

    public void setPublicacoes_media(List<PostMultimedia> publicacoes_media) {
        this.publicacoes_media = publicacoes_media;
    }

    public LocalDateTime getData_nascimento() {
        return data_nascimento;
    }

    public void setData_nascimento(LocalDateTime data_nascimento) {
        this.data_nascimento = data_nascimento;
    }

    public Grupo getGrupo() {
        return grupo;
    }

    public void setGrupo(Grupo grupo) {
        this.grupo = grupo;
    }

    public List<Gamer> getPossiveisAvaliacoes() {
        return possiveisAvaliacoes;
    }

    public void setPossiveisAvaliacoes(List<Gamer> possiveisAvaliacoes) {
        this.possiveisAvaliacoes = possiveisAvaliacoes;
    }

    /**
     * Adiona um post multimedia à lista de posts realizados por este gamer
     * @param post Publicação realizada
     * @return Booleano com a veracidade da operação
     */
    public boolean add_post_multimedia(PostMultimedia post) {
        return this.publicacoes_media.add(post);
    }

    /**
     * Adiona um post de grupo à lista de posts realizados por este gamer
     * @param post Publicação realizada
     * @return Booleano com a veracidade da operação
     */
    public boolean add_post_grupo(PostGrupo post) {
        return this.publicacoes_grupo.add(post);
    }

    @Override
    public String toString() {
        return "Gamer{" +
                "id=" + id +
                ", classificacao=" + classificacao +
                ", nome='" + nome + '\'' +
                ", estado='" + estado + '\'' +
                ", utilizador=" + utilizador +
                ", avatar=" + avatar +
                ", recompensas=" + recompensas +
                ", amigos=" + amigos +
                ", jogos=" + jogos +
                ", caixasMensagens=" + caixasMensagens +
                ", publicacoes_grupo=" + publicacoes_grupo +
                ", publicacoes_media=" + publicacoes_media +
                ", grupo=" + grupo +
                '}';
    }



    /**
     * Método que remove um post do gamer
     * @param id_post Identificador do post
     * @param tipo_post Tipo de post
     *                  0 - se for post de media
     *                  1 - se for post de grupo
     * @return Booleano com a veracidade da operação
     */
    public boolean remove_post(int id_post, int tipo_post) {
        boolean sucesso = false;
        if (tipo_post == 0) {

            Iterator<PostMultimedia> posts = this.publicacoes_media.iterator();
            while (posts.hasNext() && !sucesso) {
                PostMultimedia p = posts.next();
                if (p.getId() == id_post) {
                    this.publicacoes_media.remove(p);
                    sucesso = true;
                }
            }

        } else {

            Iterator<PostGrupo> posts = this.publicacoes_grupo.iterator();
            while (posts.hasNext() && !sucesso) {
                PostGrupo p = posts.next();
                if (p.getId() == id_post) {
                    this.publicacoes_grupo.remove(p);
                    sucesso = true;
                }
            }

        }

        return sucesso;
    }

    /**
     * Adiona um amigo ao gamer
     * @param amigo Gamer que irá ser adicionado como amigo
     */
    public void addAmigo(Gamer amigo) {
        this.amigos.add(amigo);
    }

    /**
     * Metodo que avalia um Gamer
     * @param classificacao Nova classificação
     */
    public void avalia(int classificacao) {
        this.classificacao = (((this.classificacao * this.numero_classificacoes) + classificacao) / (this.numero_classificacoes + 1));
        this.numero_classificacoes++;
    }

    /**
     * Adiciona uma nova caixa de mensagem ao gamer
     * @param caixa Novacaixa de mensagem
     */
    public void addCaixaMensagem(CaixaMensagens caixa) {
        this.caixasMensagens.add(caixa);
    }

    /**
     * Adiona jogos à lista de jogos a seguir do gamer
     * @param jogo Lista com jogos que começou a seguir
     * @return Booleano com a veracidade da operação
     */
    public boolean addJogos(List<Jogo> jogo) {
        return this.jogos.addAll(jogo);
    }

    /**
     * Remove um jogo da lista de jogos a seguir
     * @param jogo Jogo a remover
     * @return Booleano com a veracidade da operação
     */
    public boolean removeJogo(Jogo jogo) {
        return this.jogos.remove(jogo);
    }

    /**
     * Remove a amizade de um Gamer
     * @param g2 Ex-amigo
     * @return Booleano com a veracidade da operação
     */
    public boolean remove_amigo(Gamer g2) {
        return this.amigos.remove(g2);
    }

    /**
     * Remove uma caixa de mensagens de um Gamer
     * @param caixa Caixa de mensagens a remover
     */
    public void remove_caixa_mensagem(CaixaMensagens caixa) {
        this.caixasMensagens.remove(caixa);
    }
}
